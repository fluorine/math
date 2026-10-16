#!/usr/bin/env python3
"""Independent checker for a finite-board Snaky pairing certificate.

No search or geometry-constructor imports. A pairing uses disjoint free cells
and hits every placement not yet occupied by Breaker. After Maker first enters
a pair, Breaker takes its mate; extra Breaker stones can only help. On an
unpaired move Breaker takes any free cell. A final unmatched Maker move cannot
complete a placement, since every live placement still has a blocking pair.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def winning_sets(n):
    forms = set()
    for reflection in (1, -1):
        shape = [(0, 0), (1, 0), (2, 0), (3, 0), (3, reflection), (4, reflection)]
        for _ in range(4):
            left = min(p[0] for p in shape)
            bottom = min(p[1] for p in shape)
            forms.add(tuple(sorted((x - left, y - bottom) for x, y in shape)))
            shape = [(-y, x) for x, y in shape]
    result = set()
    for shape in forms:
        for y in range(n):
            for x in range(n):
                cells = tuple((x + dx, y + dy) for dx, dy in shape)
                if all(0 <= a < n and 0 <= b < n for a, b in cells):
                    result.add(frozenset(b * n + a for a, b in cells))
    return result


def check(n, pairs, maker=(), breaker=()):
    if type(n) is not int or n < 1:
        raise ValueError("invalid square size")
    board = set(range(n * n))
    if any(type(q) is not int for q in (*maker, *breaker)):
        raise ValueError("occupancy must contain integer cells")
    maker, breaker = set(maker), set(breaker)
    if not maker <= board or not breaker <= board or maker & breaker:
        raise ValueError("invalid initial occupancy")
    free = board - maker - breaker
    used, accepted = set(), []
    for pair in pairs:
        if len(pair) != 2 or any(type(q) is not int for q in pair) or pair[0] == pair[1]:
            raise ValueError("each pair needs two different integer cells")
        pair = set(pair)
        if not pair <= free:
            raise ValueError("pair cell is not free")
        if pair & used:
            raise ValueError("pair cells overlap")
        used |= pair
        accepted.append(pair)
    edges = winning_sets(n)
    live = [edge for edge in edges if not edge & breaker]
    for edge in live:
        if edge <= maker:
            raise ValueError("Maker already owns a Snaky before Breaker's reply")
        if not any(pair <= edge for pair in accepted):
            raise ValueError(f"uncovered live placement: {sorted(edge)}")
    return dict(status="valid_pairing", size=n, placements=len(edges),
                live_placements=len(live), pairs=len(accepted),
                empty_board=not maker and not breaker)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    if data.get("schema") != "snaky-static-pairing-v1":
        raise ValueError("unrecognized certificate schema")
    print(json.dumps(check(data["size"], data["pairs"], data.get("maker", []),
                           data.get("breaker", [])), sort_keys=True))


if __name__ == "__main__":
    main()
