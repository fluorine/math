#!/usr/bin/env python3
"""Summarize which remembered stones and safe cells enable the construction.

This descriptive audit uses constructor geometry and is not independent
verification. Exact state and transform witnesses remain in the run report.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

from analyze_routes import ORIENTS, parse, transform


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", type=Path)
    ap.add_argument("run_report", type=Path)
    ap.add_argument("compact_map", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    cards, meta = parse(args.certificate)
    run = json.loads(args.run_report.read_text())
    idmap = {r["combined_id"]: r for r in json.loads(args.compact_map.read_text())["cards"]}
    classifications = Counter()
    sources = Counter()
    leaves = defaultdict(list)
    for hit in run["catalog_hits"]:
        state, hint = hit["state"], hit["hint"]
        baseline = cards[state["baseline_card"]]
        candidate = cards[hint["child"]]
        old_g = tuple(state["transform"])
        new_g = (*ORIENTS[hint["orientation"]], *hint["translation"])
        old_a = {transform(old_g, q) for q in baseline.required}
        old_s = {transform(old_g, q) for q in baseline.support}
        new_a = {transform(new_g, q) for q in candidate.required}
        new_s = {transform(new_g, q) for q in candidate.support}
        extra_a, extra_s = new_a - old_a, new_s - old_s
        category = ("retained_maker_and_expanded_support" if extra_a else
                    "expanded_support_only") if extra_s else "no_support_expansion"
        classifications[category] += 1
        origin = idmap[hint["child"]]
        sources[origin["source"]] += 1
        leaves[hint["child"]].append(dict(
            baseline_card=state["baseline_card"], budget=state["remaining_maker_moves"],
            extra_maker=sorted(extra_a), extra_support=sorted(extra_s),
            transformed_move=transform(new_g, candidate.move), state=state, hint=hint))
    report = dict(schema="snaky-shortcut-audit-v1", candidate_sha256=meta["source_sha256"],
                  shortcut_count=len(run["catalog_hits"]), classifications=dict(classifications),
                  occurrences_by_source=dict(sources), distinct_tactic_count=len(leaves),
                  distinct_tactics_by_source=dict(Counter(idmap[j]["source"] for j in leaves)),
                  zero_cost_pass_count=run["constructor_stats"].get("zero_cost_passes", 0),
                  tactics=[])
    for j, uses in sorted(leaves.items()):
        report["tactics"].append(dict(
            **idmap[j], height=cards[j].height, occurrences=len(uses),
            baseline_cards=sorted({u["baseline_card"] for u in uses}),
            maximum_extra_maker_cells=max(len(u["extra_maker"]) for u in uses),
            maximum_extra_support_cells=max(len(u["extra_support"]) for u in uses),
            representative=uses[0]))
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("shortcut_count", "classifications",
                                            "occurrences_by_source", "distinct_tactics_by_source",
                                            "zero_cost_pass_count")}))


if __name__ == "__main__":
    main()
