#!/usr/bin/env python3
"""Recompute a fixed explicit seed and certify its comparison using exact integers."""
import argparse
from decimal import Decimal
import json
from pathlib import Path

from label_contract import SuccinctTournament
from recurrences import certify, seed


def certificate():
    q, depth = 1001, 17
    g = SuccinctTournament(q)
    # Optimize the stronger immediate SOURCE baseline, then keep the exact
    # same number of copies for our structural comparison.
    baseline = seed(depth,g.M,"immediate",certified_or=True)
    copies = baseline["copies"]
    structural = seed(depth,g.M,"structural",copies=copies)
    baseline, structural = certify(baseline), certify(structural)
    # Do not make certificate equality depend on the platform's libm rounding.
    baseline.pop("alpha_approx")
    structural.pop("alpha_approx")
    assert baseline["B"] == structural["B"]
    assert baseline["n"] == structural["n"]
    assert 1 < structural["A"] < baseline["A"]
    assert baseline["B"] > baseline["A"]**2
    assert Decimal(structural["alpha_interval"][0]) > Decimal(baseline["alpha_interval"][1])
    assert g.k <= q**13
    assert g.r == 13*(q-1) and g.M == g.r*g.r
    assert baseline["alpha_certificate"]["lower_numerator"] >= 20154
    # Coarse published theorem has an especially simple independently
    # certifiable instance within the same uniform label family.
    d0 = 9
    q0 = max(3,1+(3**(d0+1)+12)//13)
    coarse = SuccinctTournament(q0)
    assert coarse.M >= 9**(d0+1)
    A0, B0 = 22*coarse.M**10, coarse.M**2*coarse.k**9
    n0 = 11*coarse.M**2*(coarse.k*coarse.r)**9
    assert 121*B0 >= 128*A0*A0
    return {
        "status":"proved bounds with finite arithmetic certificates; see written proofs",
        "parameters":{"q":q,"digit_length":13,"depth":depth,"M":g.M,"r":g.r,
                      "k":g.k,"OR_copies":copies},
        "baseline":baseline,"structural":structural,
        "same_seed_comparison":{"same_B":True,"same_dimension":True,
                                "sensitivity_bound_reduction":baseline["A"]-structural["A"],
                                "strict_alpha_improvement":True},
        "published_coarse_instance":{"depth":d0,"q":q0,"M":coarse.M,"r":coarse.r,
                                     "A":A0,"B":B0,"n":n0,
                                     "exact_inequality":"121*B >= 128*A^2"},
        "large_tournaments_or_truth_tables_materialized":0,
        "novelty_scope":"Explicit exact-contract labels and structural profile bound; source formula optimization is baseline. Historical novelty remains provisional."
    }


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",type=Path)
    parser.add_argument("--check",type=Path)
    args=parser.parse_args()
    result=certificate()
    if args.check:
        assert json.loads(args.check.read_text()) == result, "saved certificate differs from recomputation"
    if args.write:
        args.write.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"passed","parameters":result["parameters"],
                      "baseline_alpha":result["baseline"]["alpha_interval"],
                      "structural_alpha":result["structural"]["alpha_interval"],
                      "dimension_digits":result["structural"]["dimension_digits"],
                      "same_seed_strict_improvement":True},indent=2))


if __name__=="__main__":
    main()
