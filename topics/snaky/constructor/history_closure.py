#!/usr/bin/env python3
"""Try to shorten a baseline policy using full history and an existing catalog.

No arbitrary Maker-move search: use a certified catalog tactic if it fits in
the remaining budget; otherwise follow the baseline move and recurse only
on responses whose baseline height exceeds the remaining budget. Repeated
baseline pivots are skipped through their pass hint without spending a move.
Every successful result is exported as ordinary snaky-cards-txt-v1 cards.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import time

from analyze_routes import Card, Hint, ORIENTS, compose, parse, transform, winning_placement


class LimitReached(Exception):
    pass


@dataclass(frozen=True)
class PlacementFamily:
    height: int
    card: int
    orientation: int
    min_x: int
    min_y: int
    required_offsets: tuple[int, ...]
    support_mask: int
    allowed_bases: int


class Catalog:
    def __init__(self, cards, rows, columns, deadline):
        self.cards = cards
        self.width = columns
        self.deadline = deadline
        self.families = []
        self.stats = Counter()
        self.cache = {}
        seen = set()
        for i, card in enumerate(cards):
            if not card.required <= card.support:
                raise ValueError("catalog requires A subset S")
            for o, orient in enumerate(ORIENTS):
                g = (*orient, 0, 0)
                support = [transform(g, q) for q in card.support]
                min_x, min_y = min(x for x, _ in support), min(y for _, y in support)
                width = max(x for x, _ in support) - min_x + 1
                height = max(y for _, y in support) - min_y + 1
                if width > columns or height > rows:
                    continue
                required = sorted(transform(g, q) for q in card.required)
                offsets = tuple((y - min_y) * columns + x - min_x for x, y in required)
                support_mask = sum(1 << ((y - min_y) * columns + x - min_x)
                                   for x, y in support)
                bases = sum(1 << (y * columns + x)
                            for y in range(rows - height + 1)
                            for x in range(columns - width + 1))
                key = (card.height, offsets, support_mask, bases)
                # If A,S,h agree, either legal move/proof is sufficient.
                if key in seen:
                    continue
                seen.add(key)
                self.families.append(PlacementFamily(card.height, i, o, min_x, min_y,
                                                      offsets, support_mask, bases))
        self.families.sort(key=lambda f: (f.height, len(f.required_offsets), f.card))

    def find(self, maker, available, budget):
        key = (maker, available, budget)
        if key in self.cache:
            self.stats["cache_hits"] += 1
            return self.cache[key]
        self.stats["queries"] += 1
        if time.monotonic() >= self.deadline:
            raise LimitReached("wall time limit")
        n = bin(maker).count("1")
        for family in self.families:
            if family.height > budget:
                break
            if len(family.required_offsets) > n:
                continue
            self.stats["families_examined"] += 1
            possible = family.allowed_bases
            for offset in family.required_offsets:
                possible &= maker >> offset
                if not possible:
                    break
            while possible:
                low = possible & -possible
                base = low.bit_length() - 1
                possible ^= low
                self.stats["support_tests"] += 1
                if (family.support_mask << base) & ~available:
                    continue
                x, y = base % self.width, base // self.width
                hint = Hint(family.card, family.orientation,
                            x - family.min_x, y - family.min_y)
                self.cache[key] = hint
                self.stats["hits"] += 1
                return hint
        self.cache[key] = None
        return None


class Constructor:
    def __init__(self, cards, meta, catalog, deadline, node_limit):
        self.cards = list(cards)
        self.baseline_count = len(cards)
        self.meta = meta
        self.width = meta["columns"]
        self.catalog = catalog
        self.deadline = deadline
        self.node_limit = node_limit
        self.root_xf = tuple(meta["root_transform"])
        self.universe = frozenset(transform(self.root_xf, q)
                                  for q in cards[meta["root"]].support)
        self.universe_mask = self.mask(self.universe)
        self.memo = {}
        self.stats = Counter()
        self.trace = []
        self.first_failure = None
        self.catalog_hits = []

    def mask(self, points):
        return sum(1 << (y * self.width + x) for x, y in points)

    def points(self, mask):
        out = []
        while mask:
            bit = mask & -mask
            q = bit.bit_length() - 1
            out.append((q % self.width, q // self.width))
            mask ^= bit
        return frozenset(out)

    def global_hint(self, hint, g):
        xf = compose(g, hint.xf)
        return Hint(hint.child, ORIENTS.index(xf[:4]), xf[4], xf[5])

    def state(self, i, g, maker, breaker, budget):
        return dict(baseline_card=i, transform=list(g), remaining_maker_moves=budget,
                    maker=sorted(self.points(maker)), breaker=sorted(self.points(breaker)))

    def solve(self, i, g, maker, breaker, budget):
        self.stats["calls"] += 1
        if self.stats["calls"] > self.node_limit:
            raise LimitReached("node limit")
        if time.monotonic() >= self.deadline:
            raise LimitReached("wall time limit")
        key = (i, g, maker, breaker, budget)
        if key in self.memo:
            self.stats["memo_hits"] += 1
            return self.memo[key]
        card = self.cards[i]
        if card.height <= budget:
            self.stats["baseline_leaves"] += 1
            return Hint(i, ORIENTS.index(g[:4]), g[4], g[5])
        if budget < 1:
            if self.first_failure is None:
                self.first_failure = self.state(i, g, maker, breaker, budget)
            return None
        available = self.universe_mask & ~breaker
        hint = self.catalog.find(maker, available, budget)
        if hint is not None:
            self.stats["catalog_leaves"] += 1
            self.catalog_hits.append(dict(state=self.state(i, g, maker, breaker, budget),
                                          hint=hint.json()))
            self.memo[key] = hint
            return hint
        p = transform(g, card.move)
        p_bit = 1 << (p[1] * self.width + p[0])
        if p_bit & breaker or not p_bit & available:
            raise AssertionError("baseline pivot is blocked")
        if p_bit & maker:
            if card.outside is None:
                raise AssertionError("nonterminal repeated pivot has no pass")
            self.stats["zero_cost_passes"] += 1
            h = card.outside
            result = self.solve(h.child, compose(g, h.xf), maker, breaker, budget)
            self.memo[key] = result
            return result
        next_maker = maker | p_bit
        owned = self.points(next_maker)
        if winning_placement(owned) is not None:
            synthesized = Card(1, p, self.points(maker), self.points(available), None, [])
            j = len(self.cards)
            self.cards.append(synthesized)
            self.stats["terminal_cards"] += 1
            result = Hint(j, 0, 0, 0)
            self.memo[key] = result
            return result
        if budget == 1:
            if self.first_failure is None:
                self.first_failure = self.state(i, g, maker, breaker, budget)
            self.memo[key] = None
            return None
        if card.outside is None:
            raise AssertionError("unwon baseline card has no pass hint")
        support = frozenset(transform(g, q) for q in card.support)
        reply_map = {transform(g, w): h for w, h in card.replies}
        branches = [(None, card.outside)]
        branches += [(w, reply_map[w] if w in support else card.outside)
                     for w in sorted(self.points(available & ~next_maker))]
        # The expensive branches are tried before automatic certified leaves.
        branches.sort(key=lambda wh: -self.cards[wh[1].child].height)
        output = []
        for w, h in branches:
            child_g = compose(g, h.xf)
            next_breaker = breaker if w is None else breaker | (1 << (w[1] * self.width + w[0]))
            self.trace.append(dict(card=i, maker_move=p, breaker_reply=w,
                                   next_card=h.child, remaining=budget))
            result = self.solve(h.child, child_g, next_maker, next_breaker, budget - 1)
            if result is None:
                if self.first_failure is not None and "trace" not in self.first_failure:
                    self.first_failure["trace"] = list(self.trace)
                self.trace.pop()
                self.memo[key] = None
                return None
            self.trace.pop()
            output.append((w, result))
        outside = next(h for w, h in output if w is None)
        replies = [(w, h) for w, h in output if w is not None]
        actual_height = 1 + max(self.cards[h.child].height for _, h in output)
        if actual_height > budget:
            raise AssertionError("constructed height exceeds budget")
        j = len(self.cards)
        self.cards.append(Card(actual_height, p, self.points(maker),
                               self.points(available), outside, replies))
        self.stats["internal_cards"] += 1
        result = Hint(j, 0, 0, 0)
        self.memo[key] = result
        return result


def serialize(cards, meta, root):
    lines = [f"snaky-cards-txt-v1 {meta['rows']} {meta['columns']} "
             f"{root.child} {root.orientation} {root.dx} {root.dy}"]
    for card in cards:
        row = [card.height, *card.move, len(card.required)]
        row += [v for q in sorted(card.required) for v in q]
        row += [len(card.support)]
        row += [v for q in sorted(card.support) for v in q]
        h = card.outside
        row += [-1] if h is None else [h.child, h.orientation, h.dx, h.dy]
        row += [len(card.replies)]
        for w, h in card.replies:
            row += [*w, h.child, h.orientation, h.dx, h.dy]
        lines.append(" ".join(map(str, row)))
    return "\n".join(lines) + "\n"


def append_catalog(cards, extra):
    """Preserve every imported dependency while assigning disjoint card IDs."""
    offset = len(cards)

    def shifted(h):
        return None if h is None else Hint(h.child + offset, h.orientation, h.dx, h.dy)

    cards.extend(Card(c.height, c.move, c.required, c.support, shifted(c.outside),
                      [(w, shifted(h)) for w, h in c.replies]) for c in extra)


def compact_generated_supports(cards, first_generated):
    """Discard unused safe cells after construction; all child maps stay fixed."""
    for i in range(first_generated, len(cards)):
        card = cards[i]
        needed = set(card.required) | {card.move}
        for _, hint in card.edges():
            needed.update(transform(hint.xf, q) for q in cards[hint.child].support)
        if not needed <= card.support:
            raise AssertionError("a generated child escapes the safe envelope")
        card.support = frozenset(needed)
        card.replies = [(w, h) for w, h in card.replies if w in needed]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--budget", type=int, default=19)
    ap.add_argument("--seconds", type=float, default=120)
    ap.add_argument("--nodes", type=int, default=100000)
    ap.add_argument("--extra-catalog", type=Path, action="append", default=[])
    ap.add_argument("--export-partial", action="store_true",
                    help="save verified-by-construction partial tactics with the original root bound")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    start = time.monotonic()
    deadline = start + args.seconds
    cards, meta = parse(args.certificate)
    extras = []
    for path in args.extra_catalog:
        extra, extra_meta = parse(path)
        extras.append(dict(source=str(path), offset=len(cards), card_count=len(extra),
                           source_sha256=extra_meta["source_sha256"]))
        append_catalog(cards, extra)
    catalog = Catalog(cards, meta["rows"], meta["columns"], deadline)
    ctor = Constructor(cards, meta, catalog, deadline, args.nodes)
    status, result = "complete", None
    try:
        result = ctor.solve(meta["root"], tuple(meta["root_transform"]), 0, 0, args.budget)
        status = "constructed" if result is not None else "uncovered_state"
    except LimitReached as exc:
        status = str(exc)
    report = dict(schema="snaky-history-closure-v1", status=status, input=meta,
                  extra_catalogs=extras,
                  target_maker_moves=args.budget, threads=1, randomized=False,
                  elapsed_seconds=round(time.monotonic() - start, 6),
                  wall_limit_seconds=args.seconds, node_limit=args.nodes,
                  catalog_placement_families=len(catalog.families),
                  constructor_stats=dict(ctor.stats), catalog_stats=dict(catalog.stats),
                  synthesized_card_count=len(ctor.cards) - len(cards),
                  first_uncovered_state=ctor.first_failure,
                  catalog_hits=ctor.catalog_hits,
                  limitation="Failure is for this baseline-following catalog-closure mechanism only; not a game lower bound.")
    if result is not None:
        compact_generated_supports(ctor.cards, len(cards))
        certificate = args.output.with_suffix(".cards.txt")
        certificate.write_text(serialize(ctor.cards, meta, result))
        report["candidate_certificate"] = str(certificate)
        report["candidate_root"] = result.json()
    elif args.export_partial and len(ctor.cards) > len(cards):
        compact_generated_supports(ctor.cards, len(cards))
        certificate = args.output.with_suffix(".partial.cards.txt")
        g = tuple(meta["root_transform"])
        original_root = Hint(meta["root"], ORIENTS.index(g[:4]), g[4], g[5])
        certificate.write_text(serialize(ctor.cards, meta, original_root))
        report["partial_tactic_catalog"] = str(certificate)
        report["partial_catalog_root_bound"] = cards[meta["root"]].height
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "elapsed_seconds", "constructor_stats",
                                            "catalog_stats", "synthesized_card_count")}))
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
