#!/usr/bin/env python3
"""Exhaustively audit one-move Snaky completions of a concrete plane position."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

from verify_cards import InvalidCertificate, SHAPE_ORIENTATIONS, require, winning_witness


def _point(value):
    require(isinstance(value, (list, tuple)) and len(value) == 2
            and all(type(x) is int for x in value), "point", "integer coordinate pair required")
    return tuple(value)


def _points(values):
    require(isinstance(values, list), "points", "point list required")
    points = tuple(_point(value) for value in values)
    require(len(points) == len(set(points)), "duplicates", "stone list repeats a point")
    return frozenset(points)


def one_move_completions(maker, breaker):
    """Enumerate every translated D4 placement intersecting current Maker stones.

    This finite enumeration is exhaustive for a one-move completion: a six-cell
    shape completed by one new cell must contain five existing Maker cells.
    A disjoint placement needs six new stones and cannot be a missed completion.
    """
    require(not maker.intersection(breaker), "overlap", "players own the same point")
    placements = set()
    for shape in SHAPE_ORIENTATIONS:
        for sx, sy in shape:
            for mx, my in maker:
                dx, dy = mx - sx, my - sy
                placements.add(tuple(sorted((x + dx, y + dy) for x, y in shape)))
    unblocked_histogram = Counter()
    blocked_histogram = Counter()
    completions = set()
    already_won = []
    closest = None
    closest_count = 0
    completion_placements = 0
    for placement in sorted(placements):
        cells = frozenset(placement)
        owned = len(cells.intersection(maker))
        if cells.intersection(breaker):
            blocked_histogram[owned] += 1
            continue
        unblocked_histogram[owned] += 1
        if owned > closest_count:
            closest, closest_count = placement, owned
        if owned == 6:
            already_won.append(placement)
        elif owned == 5:
            completions.update(cells - maker)
            completion_placements += 1
    return {
        "black_stones": len(maker),
        "white_stones": len(breaker),
        "raw_anchor_pairs": len(maker) * 6 * len(SHAPE_ORIENTATIONS),
        "distinct_placements_intersecting_black": len(placements),
        "unblocked_by_black_overlap": dict(sorted(unblocked_histogram.items())),
        "blocked_by_black_overlap": dict(sorted(blocked_histogram.items())),
        "already_won_placements": len(already_won),
        "one_move_completion_placements": completion_placements,
        "legal_completion_moves": [list(point) for point in sorted(completions)],
        "max_black_overlap_in_unblocked_placement": closest_count,
        "example_closest_placement": [list(point) for point in closest] if closest is not None else None,
        "cannot_win_on_next_move": not already_won and not completions,
        "enumeration_covers_all_one_move_wins_on_integer_plane": True,
        "game_wide_lower_bound_claimed": False,
    }


def audit_state(state):
    require(isinstance(state, dict), "state", "state object required")
    require(state.get("remaining_maker_moves") == 1, "budget", "this audit requires one move remaining")
    maker, breaker = _points(state.get("maker")), _points(state.get("breaker"))
    trace = state.get("trace")
    require(isinstance(trace, list), "trace", "concrete trace required")
    actual_maker, actual_breaker = set(), set()
    for turn, step in enumerate(trace, 1):
        require(isinstance(step, dict), "trace", "turn object required")
        move = _point(step.get("maker_move"))
        require(move not in actual_maker | actual_breaker, "occupied-move",
                f"Black turn {turn} is occupied")
        actual_maker.add(move)
        require(winning_witness(frozenset(actual_maker)) is None, "earlier-win",
                f"the traced game already ended on Black turn {turn}")
        reply = _point(step.get("breaker_reply"))
        require(reply not in actual_maker | actual_breaker, "occupied-move",
                f"White turn {turn} is occupied")
        actual_breaker.add(reply)
    require(actual_maker == maker and actual_breaker == breaker, "state-trace",
            "listed state differs from accumulated trace stones")
    result = one_move_completions(maker, breaker)
    result.update({"status": "verified", "geometry": "integer plane",
                   "legal_move_pairs_replayed": len(trace),
                   "remaining_black_moves": 1,
                   "selected_policy_hints_checked_by_this_run": False,
                   "scope": "only this concrete late position, after its listed legal trace"})
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args(argv)
    try:
        data = args.report.read_bytes()
        state = json.loads(data)["first_uncovered_state"]
        result = audit_state(state)
        result.update({"input_report_sha256": hashlib.sha256(data).hexdigest(),
                       "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "card_verifier_sha256": hashlib.sha256(Path(__file__).with_name("verify_cards.py").read_bytes()).hexdigest()})
    except (InvalidCertificate, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}, indent=2))
        return 1
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
