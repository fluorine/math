#!/usr/bin/env python3
"""Reconstruct the dependency DAG and replay its maximum-height routes.

This is a construction aid, not an independent certificate verifier. It never
searches for a new move. Coordinates are integer (x, y), with zero-based card
indices exactly as in snaky-cards-txt-v1. A route includes one edge for each
listed Breaker reply class, including a single outside-support class (pass).
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import time


ORIENTS = ((1, 0, 0, 1), (-1, 0, 0, 1), (0, -1, 1, 0),
           (0, 1, 1, 0), (-1, 0, 0, -1), (1, 0, 0, -1),
           (0, 1, -1, 0), (0, -1, -1, 0))
SNAKY = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
Pt = tuple[int, int]
Xf = tuple[int, int, int, int, int, int]


def transform(g: Xf, q: Pt) -> Pt:
    a, b, c, d, x, y = g
    return a * q[0] + b * q[1] + x, c * q[0] + d * q[1] + y


def compose(g: Xf, f: Xf) -> Xf:
    a, b, c, d, x, y = g
    e, f1, g1, h, u, v = f
    return (a * e + b * g1, a * f1 + b * h,
            c * e + d * g1, c * f1 + d * h,
            a * u + b * v + x, c * u + d * v + y)


@dataclass(frozen=True)
class Hint:
    child: int
    orientation: int
    dx: int
    dy: int

    @property
    def xf(self) -> Xf:
        return (*ORIENTS[self.orientation], self.dx, self.dy)

    def json(self) -> dict:
        return dict(child=self.child, orientation=self.orientation,
                    translation=[self.dx, self.dy])


@dataclass
class Card:
    height: int
    move: Pt
    required: frozenset[Pt]
    support: frozenset[Pt]
    outside: Hint | None
    replies: list[tuple[Pt, Hint]]

    def edges(self):
        if self.outside is not None:
            yield None, self.outside
        # cardOK ignores replies at cells already owned after the move.
        for w, hint in self.replies:
            if w not in self.required and w != self.move:
                yield w, hint


def parse(path: Path):
    raw = path.read_bytes()
    lines = raw.decode("ascii").splitlines()
    tag, rows, cols, root, o, dx, dy = lines[0].split()
    if tag != "snaky-cards-txt-v1":
        raise ValueError("unsupported format")
    cards = []
    for line_number, line in enumerate(lines[1:], 2):
        tokens = iter(map(int, line.split()))

        def nxt():
            return next(tokens)

        def points():
            n = nxt()
            if n < 0:
                raise ValueError("negative point count")
            pts = [(nxt(), nxt()) for _ in range(n)]
            if len(set(pts)) != n:
                raise ValueError("duplicate points")
            return frozenset(pts)

        def hint(child):
            h = Hint(child, nxt(), nxt(), nxt())
            if h.child < 0 or not 0 <= h.orientation < 8:
                raise ValueError("invalid hint index")
            return h

        try:
            height, p = nxt(), (nxt(), nxt())
            required, support = points(), points()
            child = nxt()
            outside = None if child == -1 else hint(child)
            n = nxt()
            if n < 0:
                raise ValueError("negative reply count")
            replies = [((nxt(), nxt()), hint(nxt())) for _ in range(n)]
            if len({w for w, _ in replies}) != len(replies):
                raise ValueError("duplicate reply keys")
            sentinel = object()
            if next(tokens, sentinel) is not sentinel:
                raise ValueError("trailing tokens")
        except (ValueError, StopIteration) as exc:
            raise ValueError(f"malformed card on line {line_number}: {exc}") from exc
        cards.append(Card(height, p, required, support, outside, replies))
    root_xf = (*ORIENTS[int(o)], int(dx), int(dy))
    meta = dict(format=tag, rows=int(rows), columns=int(cols), root=int(root),
                root_transform=list(root_xf), source_sha256=hashlib.sha256(raw).hexdigest())
    return cards, meta


SHAPES = tuple(tuple(transform((*g, 0, 0), q) for q in SNAKY) for g in ORIENTS)


@lru_cache(maxsize=20000)
def winning_placement(owned: frozenset[Pt]):
    if len(owned) < 6:
        return None
    for shape in SHAPES:
        for x, y in sorted(owned):
            candidate = tuple((x + u, y + v) for u, v in shape)
            if all(q in owned for q in candidate):
                return candidate
    return None


def analysis(cards, meta):
    root = meta["root"]
    critical = {}
    depths, suffix_counts = {}, {}
    for i, card in enumerate(cards):
        edges = list(card.edges())
        if any(not 0 <= h.child < i for _, h in edges):
            raise ValueError("input is not in children-first DAG order")
        terminal = winning_placement(card.required | {card.move}) is not None
        depths[i] = 1 if terminal else 1 + max(depths[h.child] for _, h in edges)
        critical[i] = [] if terminal else [
            (w, h) for w, h in edges if depths[h.child] == depths[i] - 1]
        suffix_counts[i] = 1 if terminal else sum(
            suffix_counts[h.child] for _, h in critical[i])

    reachable = set()
    stack = [root]
    while stack:
        i = stack.pop()
        if i in reachable:
            continue
        reachable.add(i)
        stack.extend(h.child for _, h in cards[i].edges())
    prefix_counts = Counter({root: 1})
    for i in reversed(range(len(cards))):
        for _, h in critical[i]:
            prefix_counts[h.child] += prefix_counts[i]
    total = suffix_counts[root]
    active = sorted(i for i in prefix_counts if prefix_counts[i])
    critical_cards = []
    for i in reversed(active):
        c = cards[i]
        critical_cards.append(dict(
            card=i, height=c.height, dependency_depth=depths[i],
            move=list(c.move), required_maker=sorted(c.required),
            support=sorted(c.support), support_size=len(c.support),
            critical_prefix_count=prefix_counts[i],
            critical_suffix_count=suffix_counts[i],
            maximum_routes_through_card=prefix_counts[i] * suffix_counts[i],
            critical_edges=[dict(reply=None if w is None else list(w),
                                 **h.json()) for w, h in critical[i]],
            noncritical_max_child_depth=max(
                (depths[h.child] for w, h in c.edges()
                 if (w, h) not in critical[i]), default=0)))

    # Enumerate only the maximum-height DAG. A first obstruction discounts
    # every suffix at once; it cannot establish a lower bound for the game.
    classifications = Counter()
    by_first_reply = defaultdict(Counter)
    by_family = defaultdict(Counter)
    trigger_cards = defaultdict(Counter)
    surviving_cards = Counter()
    surviving_edges = Counter()
    samples = {}
    witness_families = {}
    visits = 0
    root_xf = tuple(meta["root_transform"])

    def finish(kind, i, trail, first_reply, detail, family):
        count = suffix_counts[i]
        classifications[kind] += count
        by_first_reply[str(first_reply)][kind] += count
        by_family[str(family)][kind] += count
        trigger_cards[kind][i] += count
        sample = dict(kind=kind, detail=detail, route=trail)
        samples.setdefault(kind, sample)
        if kind == "legal_twenty_move_route":
            witness_families.setdefault(str(family), sample)
            for row in trail:
                surviving_cards[row["card"]] += 1
                if "next_hint" in row:
                    local = row["local_breaker_reply"]
                    surviving_edges[(row["card"], None if local is None else tuple(local),
                                     row["next_hint"]["child"])] += 1

    def replay(i, g, maker, breaker, trail, first_reply, family):
        nonlocal visits
        visits += 1
        card = cards[i]
        move = transform(g, card.move)
        if card.height == 16:
            family = i
        row = dict(maker_turn=len(trail) + 1, card=i, height=card.height,
                   transform=list(g), maker_move=list(move),
                   required_maker=sorted(transform(g, q) for q in card.required),
                   forgotten_maker=sorted(maker - {transform(g, q) for q in card.required}))
        trail = trail + [row]
        if move in maker:
            finish("repeated_maker_move", i, trail, first_reply,
                   dict(move=move), family)
            return
        if move in breaker:
            finish("maker_move_occupied_by_breaker", i, trail, first_reply,
                   dict(move=move), family)
            return
        maker = maker | {move}
        win = winning_placement(maker)
        if win is not None:
            kind = "early_win" if len(trail) < depths[root] else "legal_twenty_move_route"
            finish(kind, i, trail, first_reply,
                   dict(maker=sorted(maker), breaker=sorted(breaker),
                        winning_placement=win, maker_moves=len(trail)), family)
            return
        if not critical[i]:
            finish("terminal_does_not_win", i, trail, first_reply, {}, family)
            return
        for w, h in critical[i]:
            # Any outside-support point is equivalent for this policy. Pick
            # a fresh point outside the initial finite board for the replay.
            white = (-1000 - len(trail), -1000) if w is None else transform(g, w)
            reply_label = "outside" if w is None else tuple(white)
            first = reply_label if first_reply is None else first_reply
            next_row = dict(row, breaker_reply=list(white),
                            local_breaker_reply=None if w is None else list(w),
                            next_hint=h.json())
            next_trail = trail[:-1] + [next_row]
            if white in maker or white in breaker:
                count = suffix_counts[h.child]
                kind = "illegal_repeated_breaker_reply"
                classifications[kind] += count
                by_first_reply[str(first)][kind] += count
                by_family[str(family)][kind] += count
                trigger_cards[kind][i] += count
                samples.setdefault(kind, dict(kind=kind, detail=dict(reply=white), route=next_trail))
                continue
            replay(h.child, compose(g, h.xf), maker, breaker | {white},
                   next_trail, first, family)

    replay(root, root_xf, frozenset(), frozenset(), [], None, None)
    if sum(classifications.values()) != total:
        raise AssertionError("replay route counts do not partition the maximum DAG")

    return dict(
        schema="snaky-route-analysis-v1", input=meta,
        conventions=dict(card_ids="zero-based compact-file line number minus two",
                         coordinates="integer (x,y); route coordinates use the root frame",
                         depth="one unit per visited card, including repeated planned stones",
                         route_count="labelled response classes; outside support is one class",
                         scope="baseline dependency reconstruction, not a certificate acceptance test"),
        card_count=len(cards), root_height=cards[root].height,
        reconstructed_root_depth=depths[root], reachable_card_count=len(reachable),
        height_histogram=dict(sorted(Counter(c.height for c in cards).items())),
        declared_height_mismatches=[i for i, c in enumerate(cards) if c.height != depths[i]],
        no_op_cards=[i for i, c in enumerate(cards) if c.move in c.required],
        maximum_route_count=total, critical_card_count=len(active),
        critical_cards_by_height={str(h): [i for i in active if depths[i] == h]
                                  for h in range(depths[root], 0, -1)},
        cards_on_every_maximum_route=[i for i in active
                                     if prefix_counts[i] * suffix_counts[i] == total],
        critical_cards=critical_cards,
        replay=dict(prefix_nodes_visited=visits, classifications=dict(classifications),
                    by_first_reply=dict(by_first_reply), by_height16_family=dict(by_family),
                    first_obstruction_cards=dict(trigger_cards),
                    legal_route_count_by_card=dict(surviving_cards),
                    legal_route_count_by_edge=[dict(card=i, reply=w, child=j, count=n)
                                               for (i, w, j), n in surviving_edges.items()],
                    representative_outcomes=samples,
                    legal_route_samples_by_height16_card=witness_families))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    start = time.monotonic()
    cards, meta = parse(args.certificate)
    report = analysis(cards, meta)
    report["execution"] = dict(python=platform.python_version(),
                               threads=1, randomized=False,
                               elapsed_seconds=round(time.monotonic() - start, 6))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in (
        "card_count", "root_height", "reconstructed_root_depth", "maximum_route_count",
        "critical_card_count", "cards_on_every_maximum_route")}))
    print(json.dumps(report["replay"]["classifications"], sort_keys=True))
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
