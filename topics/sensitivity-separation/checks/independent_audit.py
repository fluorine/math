#!/usr/bin/env python3
"""Independent, bounded audit of the fixed-seed arithmetic.

This file imports no companion implementation. The recurrences below were
transcribed from publication/sensitivity-note.tex, equations (immediate),
(F0), (FJ), (ones), and (update), after reading the pinned source proof.
Only the saved scan's two reported candidates are checked; no grid is run.

Logarithms use exact integer interval arithmetic, not Decimal or libm:
  log(x) = e log(2) + 2 sum_{j >= 0} z^(2j+1)/(2j+1),
  e = floor(log_2(x)), z = (x-2^e)/(x+2^e) in [0, 1/3).
For log(2), z=1/3. After N terms the positive remainder is at most
  2 z^(2N+1) / ((2N+1)(1-z^2)).
Every multiplication and division below rounds outward on a fixed rational
lattice. Thus all reported log intervals follow from integer arithmetic and
the displayed convergent-series identity, without a library log contract.

The cap-8/cap-7 calculations keep q, d, M, r, k, C, n, and B unchanged.
They are illustrative, not an optimization. Their interpretation as bounds
requires the parameterized structural proof and, for cap 7, the cyclic-label
argument to be validated separately; arithmetic does not prove those facts.

Run directly with Python 3. This script writes only its JSON report to stdout.
Each expensive integer power has a 45-second wall-clock deadline on POSIX.
"""

from functools import lru_cache
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import re
import signal
import time


ROOT = Path(__file__).resolve().parents[1]
SCALE = 10**100
TERMS = 120
POWER_TIMEOUT = 45
PINNED_REVISION = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
SOURCE_PREFIX = (
    "preprints/A-superquadratic-separation-between-sensitivity-and-block-"
    "sensitivity-September-25-2026/build/sections/"
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def ceildiv(n, d):
    return -(-n // d)


def equation(tex, label):
    match = re.search(
        r"\\label\{" + re.escape(label) + r"\}(.*?)\\end\{equation\}",
        tex,
        re.S,
    )
    require(match is not None, "missing source equation: " + label)
    return match.group(1)


def log_series(num, den):
    """Enclose 2 atanh(num/den) in integer multiples of 1/SCALE."""
    require(0 <= 3 * num <= den, "series argument is outside [0, 1/3]")
    if num == 0:
        return 0, 0
    zlo, zhi = num * SCALE // den, ceildiv(num * SCALE, den)
    z2lo = num * num * SCALE // (den * den)
    z2hi = ceildiv(num * num * SCALE, den * den)
    plo, phi = zlo, zhi
    lo = hi = 0
    for j in range(TERMS):
        odd = 2 * j + 1
        lo += 2 * plo // odd
        hi += ceildiv(2 * phi, odd)
        plo = plo * z2lo // SCALE
        phi = ceildiv(phi * z2hi, SCALE)
    hi += ceildiv(2 * phi * SCALE, (2 * TERMS + 1) * (SCALE - z2hi))
    return lo, hi


@lru_cache(maxsize=32)
def log_integer(n):
    require(1 <= n and n.bit_length() <= 8192, "log input exceeds audit bounds")
    e = n.bit_length() - 1
    two_to_e = 1 << e
    lo, hi = log_series(n - two_to_e, n + two_to_e)
    l2, u2 = log_series(1, 3)
    return e * l2 + lo, e * u2 + hi


def exponent_interval(A, B):
    alo, ahi = log_integer(A)
    blo, bhi = log_integer(B)
    require(alo > 0, "exponent denominator is not positive")
    lo, hi = Fraction(blo, ahi), Fraction(bhi, alo)
    require(lo <= hi and hi - lo < Fraction(1, 10**90), "loose log interval")
    return lo, hi


def decimal_interval(interval, places=90):
    """Print enclosing decimal endpoints using integer directed rounding."""
    scale = 10**places
    lo, hi = interval
    numbers = [lo.numerator * scale // lo.denominator,
               ceildiv(hi.numerator * scale, hi.denominator)]
    return [("-" if n < 0 else "") + f"{abs(n) // scale}.{abs(n) % scale:0{places}d}"
            for n in numbers]


def within(interval, endpoints, label):
    require(Fraction(endpoints[0]) < interval[0], label + ": lower endpoint")
    require(interval[1] < Fraction(endpoints[1]), label + ": upper endpoint")


def profiles(d, M, r, mode, cap=15):
    """Return comparison entries (S0, S1, J0, J1), not exact profiles."""
    require(1 <= d <= 64 and cap >= 3, "recurrence exceeds audit bounds")
    a, b, c, e = d + (2 if mode == "published" else 1), (d + 2) * M, 0, 0
    for _ in range(d):
        if mode == "published":
            z, w = 16 * a + b + 3 * e, 16 * a + 3 * e
        elif mode == "immediate":
            z, w = cap * a + max(b + e, 3 * e), cap * a + 3 * e
        elif mode == "coupled":
            z = max(a + (cap - 1) * c,
                    a + (cap - 2) * c + b,
                    cap * c + e,
                    (cap - 2) * c + b + e,
                    (cap - 1) * c + 2 * e,
                    (cap - 3) * c + 3 * e)
            w = max(a + (cap - 1) * c,
                    a + (cap - 2) * c + e,
                    cap * c + e,
                    (cap - 1) * c + 2 * e,
                    (cap - 3) * c + 3 * e)
        else:
            raise ValueError("unknown recurrence mode: " + mode)
        one = M * M * a + r * b
        joint_one = M * M * c + r * b
        a, b, c, e = z, one, min(w, z), min(joint_one, one)
        require(0 <= c <= a and 0 <= e <= b, "invalid comparison profile")
    return a, b, c, e


def seed(d, M, r, C, mode, cap=15):
    k = 2 * M * M + 1
    s0, s1, j0, j1 = profiles(d, M, r, mode, cap)
    A, B, n = max(C * s0, s1), C * M * k**d, C * (d + 2) * M * (k * r)**d
    return dict(S0=s0, S1=s1, A=A, B=B, n=n, dimension_digits=len(str(n)),
                final_joint_comparison_entries=[j0, j1])


def first_difference_label(tail, head, q, h):
    """Direct transcription of the publication's label equation."""
    for position in range(h):
        place = q ** (h - 1 - position)
        x, y = (tail // place) % q, (head // place) % q
        if x != y:
            return position * (q - 1) + x - int(x > y)
    raise ValueError("self edge has no first difference")


def compare_saved(actual, saved, label):
    for key in ("S0", "S1", "A", "B", "n", "dimension_digits"):
        require(actual[key] == saved[key], label + ": saved " + key + " differs")
    alpha = exponent_interval(actual["A"], actual["B"])
    within(alpha, saved["alpha_interval"], label + ": saved alpha interval")
    certificate = saved["alpha_certificate"]
    within(alpha, [Fraction(certificate["lower_numerator"], certificate["denominator"]),
                   Fraction(certificate["upper_numerator"], certificate["denominator"])],
           label + ": saved rational exponent certificate")
    require(certificate["relation"] == "A^p < B^q <= A^(p+1)",
            label + ": unexpected certificate interpretation")
    if "alpha_approx" in saved:
        require(abs(saved["alpha_approx"] - float(alpha[0])) < 1e-14,
                label + ": floating approximation differs materially")
    return alpha


def bounded_power(base, exponent):
    require(0 < exponent and base.bit_length() * exponent <= 12_000_000,
            "integer power exceeds the fixed audit size bound")
    require(hasattr(signal, "ITIMER_REAL"), "POSIX deadline support is required")

    def timeout(_signum, _frame):
        raise TimeoutError(f"integer power exceeded {POWER_TIMEOUT} seconds")

    old_handler = signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, POWER_TIMEOUT)
    try:
        return pow(base, exponent)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)


def source_hashes():
    manifest = json.loads((ROOT / "sources/manifest.json").read_text())
    results = {}
    for name in ("01-construction.tex", "02-recurrences.tex"):
        source_path = SOURCE_PREFIX + name
        record = next(item for item in manifest if item["path"] == source_path)
        require(record["revision"] == PINNED_REVISION, "source revision changed")
        cached = ROOT / ".cache/openai_math" / source_path
        if cached.exists():
            digest = hashlib.sha256(cached.read_bytes()).hexdigest()
            require(digest == record["sha256"], "pinned source hash differs: " + name)
            results[name] = digest
        else:
            results[name] = "not cached; no network access attempted"
    return results


def main():
    started = time.monotonic()
    tex_bytes = (ROOT / "publication/sensitivity-note.tex").read_bytes()
    tex = tex_bytes.decode()
    fixed = equation(tex, "eq:fixed")
    params = {name: int(re.search(r"\b" + name + r"=(\d+)", fixed).group(1))
              for name in ("q", "d", "M", "r", "k", "C")}
    require(tuple(params.values()) == (1001, 17, 169000000, 13000,
                                      57122000000000001, 164900179),
            "publication is no longer the assigned fixed seed")
    q, d, M, r, k, C = (params[key] for key in ("q", "d", "M", "r", "k", "C"))
    h = int(re.search(r"M=\[(\d+)\(q-1\)\]\^2", equation(tex, "eq:family")).group(1))
    require(r == h * (q - 1) and M == r * r and k == 2 * M * M + 1,
            "source parameter identities fail")
    require(h == 13 and k <= q**h and isqrt(M) == r, "label family does not fit")
    saved = json.loads((ROOT / "checks/seed-certificate.json").read_text())
    expected_parameters = dict(q=q, digit_length=h, depth=d, M=M, r=r, k=k, OR_copies=C)
    require(saved["parameters"] == expected_parameters, "saved parameters differ from TeX")

    # Check the rational interval engine against nontrivial log identities.
    l2, u2 = log_integer(2)
    require(Fraction(2, 3) < Fraction(l2, SCALE) < Fraction(u2, SCALE) < Fraction(25, 36),
            "log(2) is outside the elementary one-term enclosure")
    l3, u3 = log_integer(3)
    l6, u6 = log_integer(6)
    require(l2 + l3 <= u6 and l6 <= u2 + u3, "log addition identity failed")

    cases = {}
    intervals = {}
    for label, mode in (("baseline", "immediate"), ("structural", "coupled")):
        actual = seed(d, M, r, C, mode)
        old_saved = saved[label]
        for key, expected in (("d", d), ("M", M), ("r", r), ("copies", C)):
            require(old_saved[key] == expected, label + ": saved " + key + " differs")
        require(old_saved["mode"] == ("structural" if mode == "coupled" else mode),
                label + ": saved mode differs")
        alpha = compare_saved(actual, old_saved, label)
        tex_name = "old" if label == "baseline" else "new"
        claim = re.search(r"(\d+\.\d+)&<\\alpha_\\" + tex_name + r"<(\d+\.\d+)", tex)
        require(claim is not None, "missing printed exponent interval")
        within(alpha, claim.groups(), label + ": printed exponent interval")
        raw_claim = re.search(r"(\d+)\\cdot10\^\{(\d+)\}&<A_\\" + tex_name +
                              r"<(\d+)\\cdot10\^\{(\d+)\}", tex)
        require(raw_claim is not None, "missing printed sensitivity enclosure")
        a, b, c, e = map(int, raw_claim.groups())
        require(a * 10**b < actual["A"] < c * 10**e, "printed A enclosure fails")
        cases[label] = actual
        intervals[label] = alpha

    dimension_claim = re.search(r"The integer \$n\$ has \$(\d+)\$ decimal digits", tex)
    require(dimension_claim is not None, "missing printed dimension digit count")
    require(cases["baseline"]["dimension_digits"] == int(dimension_claim.group(1)),
            "printed dimension digit count differs")
    old, new = cases["baseline"], cases["structural"]
    require(new["B"] == old["B"] and new["n"] == old["n"], "the seed changed")
    require(1 < new["A"] < old["A"], "no strict sensitivity-bound improvement")
    expected_comparison = dict(same_B=True, same_dimension=True,
                              sensitivity_bound_reduction=old["A"] - new["A"],
                              strict_alpha_improvement=True)
    require(saved["same_seed_comparison"] == expected_comparison,
            "saved comparison differs")

    power_claim = re.search(r"A_\*\^\{(\d+)\}<B\^\{(\d+)\}\\le A_\*\^\{(\d+)\}",
                            equation(tex, "eq:powercert"))
    require(power_claim is not None, "missing printed power certificate")
    lower_power, b_power, upper_power = map(int, power_claim.groups())
    require((lower_power, b_power, upper_power) == (20154, 10000, 20155),
            "power certificate changed")
    power_started = time.monotonic()
    B_power = bounded_power(old["B"], b_power)
    for label in ("baseline", "structural"):
        A_power = bounded_power(cases[label]["A"], lower_power)
        require(A_power < B_power <= A_power * cases[label]["A"],
                label + ": exact integer power certificate fails")
    power_seconds = time.monotonic() - power_started

    # Only the two bracketing C values at this one baseline seed are compared.
    floor_C = old["S1"] // old["S0"]
    brackets = sorted({max(1, floor_C), max(1, ceildiv(old["S1"], old["S0"]))})
    require(C in brackets, "chosen C is not a bracketing baseline candidate")
    alternative_C = next(c for c in brackets if c != C)
    alternative = seed(d, M, r, alternative_C, "immediate")
    require(intervals["baseline"][0] > exponent_interval(alternative["A"], alternative["B"])[1],
            "chosen C does not beat the other bracketing baseline candidate")
    require(M * k**d > old["S0"], "OR optimization monotonicity condition fails")

    active_digits = 1
    while q**active_digits < k:
        active_digits += 1
    require(active_digits == 6 and q**5 < k < q**6, "active digit count differs")
    require(q - 1 <= M * M, "final-digit buckets need not be transitively oriented")
    witness = [0, 1] + [q**power for power in range(1, active_digits)]
    require(len(witness) == 7 and witness[-1] < M * M < k,
            "seven-vertex witness does not fit the transitive cyclic interval")
    incoming_labels = {}
    witness_edges = 0
    for j, head in enumerate(witness):
        labels = set()
        for tail in witness[:j]:
            require(1 <= (head - tail) % k <= M * M,
                    "witness edge is not directed from smaller to larger")
            label = first_difference_label(tail, head, q, h)
            require(0 <= label < r, "witness label is outside the palette")
            labels.add(label)
            witness_edges += 1
        require(len(labels) <= 1, "witness is not head-coherent")
        incoming_labels[str(head)] = sorted(labels)
    require(witness_edges == 21, "not all witness pairs were checked")
    sharper = {}
    for cap in (active_digits + 2, active_digits + 1):
        rows = {}
        cap_intervals = {}
        for mode in ("immediate", "coupled"):
            result = seed(d, M, r, C, mode, cap)
            require(result["n"] == old["n"] and result["B"] == old["B"],
                    "sharper-cap comparison changed the seed")
            alpha = exponent_interval(result["A"], result["B"])
            rows[mode] = {key: result[key] for key in ("S0", "S1", "A")}
            rows[mode]["alpha_interval"] = decimal_interval(alpha)
            cap_intervals[mode] = alpha
        require(rows["coupled"]["A"] < rows["immediate"]["A"],
                "sharper cap does not preserve the coupled improvement")
        baseline_beats_published = cap_intervals["immediate"][0] > intervals["structural"][1]
        published_beats_baseline = intervals["structural"][0] > cap_intervals["immediate"][1]
        require(baseline_beats_published or published_beats_baseline,
                "precision is insufficient to compare the sharper baseline")
        rows["immediate_beats_published_cap_15_coupled"] = baseline_beats_published
        rows["immediate_minus_published_cap_15_coupled_interval"] = decimal_interval(
            (cap_intervals["immediate"][0] - intervals["structural"][1],
             cap_intervals["immediate"][1] - intervals["structural"][0]))
        rows["alpha_gain_from_coupling_interval"] = decimal_interval(
            (cap_intervals["coupled"][0] - cap_intervals["immediate"][1],
             cap_intervals["coupled"][1] - cap_intervals["immediate"][0]))
        sharper[str(cap)] = rows

    coarse_d = 9
    coarse_q = max(3, 1 + ceildiv(3**(coarse_d + 1), h))
    coarse_r = h * (coarse_q - 1)
    coarse_M = coarse_r**2
    coarse_k = 2 * coarse_M**2 + 1
    coarse_A = 2 * (coarse_d + 2) * coarse_M**(coarse_d + 1)
    coarse_B = coarse_M**2 * coarse_k**coarse_d
    coarse_n = (coarse_d + 2) * coarse_M**2 * (coarse_k * coarse_r)**coarse_d
    coarse_expected = dict(depth=coarse_d, q=coarse_q, M=coarse_M, r=coarse_r,
                           A=coarse_A, B=coarse_B, n=coarse_n,
                           exact_inequality="121*B >= 128*A^2")
    require(saved["published_coarse_instance"] == coarse_expected, "saved coarse instance differs")
    require(121 * coarse_B >= 128 * coarse_A**2, "coarse rational inequality fails")

    scan = json.loads((ROOT / "checks/baseline-scan.json").read_text())
    scan_checks = {}
    for label in ("published", "immediate"):
        row = scan["best"][label]
        scan_r = isqrt(row["M"]) + (isqrt(row["M"])**2 != row["M"])
        require(row["r"] == scan_r and row["mode"] == label, "scan metadata differs")
        actual = seed(row["d"], row["M"], scan_r, row["copies"], label)
        scan_checks[label] = decimal_interval(compare_saved(actual, row, "scan " + label))

    for label in cases:
        cases[label]["alpha_interval"] = decimal_interval(intervals[label])
        cases[label]["log_A_scaled_interval"] = list(log_integer(cases[label]["A"]))
    report = dict(
        status="all independent arithmetic checks passed",
        publication_sha256=hashlib.sha256(tex_bytes).hexdigest(),
        pinned_source_hashes=source_hashes(),
        parameters=expected_parameters,
        published_cap_15=cases,
        exact_power_certificate=dict(lower_A_exponent=lower_power, B_exponent=b_power,
                                     upper_A_exponent=upper_power, B_power_bits=B_power.bit_length(),
                                     passed_for_both_A=True, elapsed_seconds=round(power_seconds, 3),
                                     timeout_seconds_per_power=POWER_TIMEOUT),
        rational_log_certificate=dict(scale=str(SCALE), terms=TERMS,
                                      log_B_scaled_interval=list(log_integer(old["B"])),
                                      method="positive atanh series, exact outward integer rounding, geometric tail bound"),
        OR_baseline_bracketing_candidates=brackets,
        OR_baseline_chosen_C_certified_better=True,
        effective_label_parameters=dict(active_digits=active_digits, fixed_leading_zero_digits=h-active_digits,
                                        arbitrary_orientation_cap=active_digits+2,
                                        cyclic_transitive_final_bucket_cap=active_digits+1),
        seven_vertex_coherent_witness=dict(vertices=witness, edges_checked=witness_edges,
                                           incoming_labels=incoming_labels,
                                           conclusion="Lower bound 7 verified; the separate upper-bound proof makes the maximum exactly 7."),
        same_seed_same_C_sharper_caps=sharper,
        coarse_saved_instance_verified=True,
        saved_scan_candidate_intervals_verified=scan_checks,
        comparison_scope=("Illustrative fixed-seed comparison, not global optimization. The cap-15 "
                          "comparison is fair at the explicitly stated contract and is arithmetically "
                          "correct. The cap-8 and cap-7 source-derived baselines both improve but remain "
                          "below the published cap-15 coupled exponent; coupling improves each matching "
                          "sharper-cap baseline. The publication acknowledges cap 8 and disclaims "
                          "optimization of this seed."),
        limitations=["The parameterized coupled formulas require a separate structural-proof review.",
                     "The cap-7 interpretation requires the separate cyclic-label proof review.",
                     "This is not a truth-table calculation of exact sensitivity or a formal proof replay.",
                     "Only the two saved scan candidates were checked; scan coverage and optimality were not audited."],
        elapsed_seconds=round(time.monotonic()-started, 3),
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
