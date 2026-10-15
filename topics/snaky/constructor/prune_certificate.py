#!/usr/bin/env python3
"""Remove unreachable cards, preserve all rules, and index children first."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from analyze_routes import Card, Hint, ORIENTS, parse
from history_closure import serialize


def prune(cards, root):
    order, active, done = [], set(), set()

    def visit(i):
        if i in active:
            raise ValueError("cycle in certificate")
        if i in done:
            return
        active.add(i)
        card = cards[i]
        hints = ([card.outside] if card.outside else []) + [h for _, h in card.replies]
        for hint in hints:
            if cards[hint.child].height >= card.height:
                raise ValueError("nondecreasing height")
            visit(hint.child)
        active.remove(i)
        done.add(i)
        order.append(i)

    visit(root.child)
    mapping = {old: new for new, old in enumerate(order)}

    def remap(h):
        return None if h is None else Hint(mapping[h.child], h.orientation, h.dx, h.dy)

    result = [Card(cards[i].height, cards[i].move, cards[i].required, cards[i].support,
                   remap(cards[i].outside), [(w, remap(h)) for w, h in cards[i].replies])
              for i in order]
    return result, remap(root), order


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--map", type=Path, required=True)
    ap.add_argument("--first-source-size", type=int, default=1738)
    ap.add_argument("--second-source-size", type=int, default=8671)
    args = ap.parse_args()
    cards, meta = parse(args.certificate)
    g = tuple(meta["root_transform"])
    root = Hint(meta["root"], ORIENTS.index(g[:4]), g[4], g[5])
    compact, root, order = prune(cards, root)
    raw = serialize(compact, meta, root).encode("ascii")
    args.output.write_bytes(raw)
    first, second = args.first_source_size, args.second_source_size

    def origin(i):
        if i < first:
            return "20_move_catalog", i
        if i < first + second:
            return "15x15_catalog", i - first
        return "constructed", i - first - second

    report = dict(schema="snaky-prune-map-v1", input_sha256=meta["source_sha256"],
                  output_sha256=hashlib.sha256(raw).hexdigest(),
                  input_cards=len(cards), output_cards=len(compact),
                  original_root=meta["root"], compact_root=root.json(),
                  root_height=compact[root.child].height,
                  source_counts=dict(Counter(origin(i)[0] for i in order)),
                  cards=[dict(compact_id=j, combined_id=i, source=origin(i)[0],
                              source_id=origin(i)[1]) for j, i in enumerate(order)])
    args.map.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("input_cards", "output_cards", "compact_root",
                                            "root_height", "source_counts", "output_sha256")}))


if __name__ == "__main__":
    main()
