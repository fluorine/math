#!/usr/bin/env python3
"""Exact recurrence arithmetic; finite scans are baseline, never novelty evidence."""
import argparse
import json
import math
import resource
import signal
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path


def step(v, M, r, mode):
    a, b, c, e = v
    if mode == "published":
        zero, joint = 16*a+b+3*e, 16*a+3*e
    elif mode == "immediate":
        zero, joint = 15*a+max(b+e, 3*e), 15*a+3*e
    elif mode == "structural":
        zero = max(a+14*c, a+13*c+b, 15*c+e, 13*c+b+e, 14*c+2*e, 12*c+3*e)
        joint = max(a+14*c, a+13*c+e, 15*c+e, 14*c+2*e, 12*c+3*e)
    else:
        raise ValueError(mode)
    one = M*M*a+r*b
    joint_one = M*M*c+r*b
    return zero, one, min(joint, zero), min(joint_one, one)


def profiles(d, M, mode="published", r=None):
    r = r or math.isqrt(M-1)+1
    a = d+2 if mode == "published" else d+1
    v = (a, (d+2)*M, 0, 0)
    for _ in range(d):
        v = step(v, M, r, mode)
    # At terminal height one there are no distinct predicate pairs.
    return v[0], v[1], 0, 0


def seed(d, M, mode="published", r=None, copies=None, certified_or=False):
    r = r or math.isqrt(M-1)+1
    a, b, _, _ = profiles(d, M, mode, r)
    k = 2*M*M+1
    block = M*k**d
    # For block>a, alpha grows below b/a, and decreases above it.
    candidates = [copies] if copies else sorted({max(1,b//a), max(1,(b+a-1)//a)})
    assert block > a, "OR optimizer requires the useful separation regime"
    results = []
    for copies in candidates:
        A = max(copies*a,b)
        B = copies*block
        n = copies*(d+2)*M*(k*r)**d
        results.append(dict(d=d,M=M,r=r,copies=copies,mode=mode,S0=a,S1=b,A=A,B=B,n=n,
                            alpha_approx=math.log(B)/math.log(A)))
    if certified_or and len(results) == 2:
        x,y = results
        xlo,xhi = map(Decimal,log_ratio_interval(x["B"],x["A"]))
        ylo,yhi = map(Decimal,log_ratio_interval(y["B"],y["A"]))
        if xlo > yhi:
            return x
        if ylo > xhi:
            return y
        raise ArithmeticError("OR candidates require higher precision to order")
    return max(results,key=lambda x:x["alpha_approx"])


def certify(item, denominator=10000):
    # Floating point only proposes a rational. Exact integer powers certify it.
    p = math.floor(item["alpha_approx"]*denominator)
    A, B = item["A"], item["B"]
    Bq = pow(B,denominator)
    while pow(A,p) >= Bq:
        p -= 1
    while pow(A,p+1) < Bq:
        p += 1
    assert pow(A,p)<Bq<=pow(A,p+1)
    item = dict(item)
    item["alpha_certificate"] = {"lower_numerator":p,"denominator":denominator,
                                  "upper_numerator":p+1,
                                  "relation":"A^p < B^q <= A^(p+1)"}
    item["dimension_digits"] = len(str(item["n"]))
    item["alpha_interval"] = log_ratio_interval(item["B"], item["A"])
    return item


def log_ratio_interval(B, A):
    """Enclose ln(B)/ln(A) using correctly rounded Decimal.ln and directed division.

    Decimal.ln is correctly rounded to nearest. Its immediate representable
    neighbors therefore bound the exact logarithm; denominator is positive.
    """
    assert B > 1 and A > 1
    with localcontext() as ctx:
        ctx.prec = 70
        loga, logb = Decimal(A).ln(), Decimal(B).ln()
        alo, ahi = loga.next_minus(), loga.next_plus()
        blo, bhi = logb.next_minus(), logb.next_plus()
        ctx.rounding = ROUND_FLOOR
        lo = blo / ahi
        ctx.rounding = ROUND_CEILING
        hi = bhi / alo
        return [str(lo),str(hi)]


def scan():
    # One thread; <=60 CPU seconds; <128 MiB of live mathematical integers
    # over this fixed domain (including the exact-power final certificates).
    # Bounded domain is reported; this is not a global integer optimization claim.
    resource.setrlimit(resource.RLIMIT_CPU,(60,60))
    signal.alarm(70)
    Ms = set(range(3,10001))
    m=10001
    while m<=10**12:
        Ms.add(m)
        m = (m*105+99)//100
    best = {}
    for mode in ("published", "immediate"):
        candidate = None
        for M in sorted(Ms):
            for d in range(1,25):
                try:
                    item=seed(d,M,mode)
                except AssertionError:
                    continue
                if candidate is None or item["alpha_approx"]>candidate["alpha_approx"]:
                    candidate=item
        best[mode]=certify(candidate)
    signal.alarm(0)
    return {"scope":"finite baseline scan; not a global optimum or novelty claim",
            "domain":{"d":[1,24],"M_dense":[3,10000],
                      "M_sparse":"ceil(1.05*M), starting 10001 through 10^12",
                      "OR_copies":"both integers bracketing S1/S0"},"best":best}


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--scan",action="store_true")
    p.add_argument("--d",type=int,default=9)
    p.add_argument("--M",type=int,default=9**10)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    result=scan() if args.scan else {mode:certify(seed(args.d,args.M,mode))
                                   for mode in ("published","immediate","structural")}
    content=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(content)
        print(args.output)
        for mode,item in result.get("best",result).items():
            print(mode, {k:item[k] for k in ("d","M","r","copies","alpha_approx","dimension_digits")})
    else:
        print(content)


if __name__=="__main__":
    main()
