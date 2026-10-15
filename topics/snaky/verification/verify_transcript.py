#!/usr/bin/env python3
"""Independently replay one concrete card-policy route, not every game branch."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from verify_cards import (
    Certificate, Hint, InvalidCertificate, MATRICES, SHAPE_ORIENTATIONS,
    normalize, parse_text, require, winning_witness,
)


def _point(value, label):
    require(isinstance(value, (list, tuple)) and len(value) == 2
            and all(type(coordinate) is int for coordinate in value),
            "transcript-format", label + " must be an integer coordinate pair")
    return tuple(value)


def _points(value, label):
    require(isinstance(value, list), "transcript-format", label + " must be a list")
    points = tuple(_point(point, label) for point in value)
    require(len(points) == len(set(points)), "transcript-format", label + " has duplicates")
    return frozenset(points)


def _apply(matrix, point):
    a, b, c, d, dx, dy = matrix
    x, y = point
    return a * x + b * y + dx, c * x + d * y + dy


def _compose(matrix, hint):
    a, b, c, d, dx, dy = matrix
    require(0 <= hint.orientation < 8, "orientation", "hint orientation must be in 0..7")
    e, f, g, h = MATRICES[hint.orientation]
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h,
            a * hint.dx + b * hint.dy + dx, c * hint.dx + d * hint.dy + dy)


def verify_transcript(certificate: Certificate, outcome: dict, plane: bool = False) -> dict:
    """Validate all claims in one outcome against actual stones and selected hints.

    This checks a line of play.  Use verify_cards.py separately for the universal
    certificate obligations.  The default requires finite-board legality; plane
    mode records off-board moves but permits them as integer-plane moves.
    """
    require(isinstance(outcome, dict) and isinstance(outcome.get("route"), list)
            and bool(outcome["route"]), "transcript-format", "nonempty route required")
    route = outcome["route"]
    black, white = set(), set()
    root = certificate.root
    require(0 <= root.orientation < 8, "orientation", "bad root orientation")
    matrix = (*MATRICES[root.orientation], root.dx, root.dy)
    index = root.card
    off_board = []
    outside_replies = 0
    witness = None
    card_indices = []

    def check_move(point, player, turn):
        require(point not in black and point not in white, "occupied-move",
                f"{player} turn {turn} tries occupied cell {point}")
        if not (0 <= point[0] < certificate.cols and 0 <= point[1] < certificate.rows):
            require(plane, "off-board", f"{player} turn {turn} at {point} is outside the board")
            off_board.append({"player": player, "black_turn": turn, "point": list(point)})

    for turn, step in enumerate(route, 1):
        require(isinstance(step, dict), "transcript-format", "each turn must be an object")
        require(step.get("maker_turn") == turn, "turn-order", f"expected Black turn {turn}")
        require(0 <= index < len(certificate.cards), "reference", f"bad route card {index}")
        card = certificate.cards[index]
        card_indices.append(index)
        require(step.get("card") == index, "route-card", f"turn {turn} has the wrong card")
        require(step.get("height") == card.height, "route-height", f"turn {turn} height mismatch")
        require(step.get("transform") == list(matrix), "route-transform",
                f"turn {turn} transform does not compose from the selected hints")
        required = frozenset(_apply(matrix, point) for point in card.required)
        region = frozenset(_apply(matrix, point) for point in card.support)
        require(required <= black, "route-requirements", f"turn {turn} lacks required Black cells")
        require(not region.intersection(white), "route-support", f"turn {turn} support meets White")
        require(_points(step.get("required_maker"), "required_maker") == required,
                "ownership-claim", f"turn {turn} required_maker claim is wrong")
        require(_points(step.get("forgotten_maker"), "forgotten_maker") == black - required,
                "ownership-claim", f"turn {turn} forgotten_maker claim is wrong")
        pivot = _apply(matrix, card.pivot)
        require(pivot in region, "pivot", f"turn {turn} pivot is outside support")
        move = _point(step.get("maker_move"), "maker_move")
        # If the pivot was already owned, the source semantics permits a legal
        # extra move anywhere. Otherwise the pivot is the required policy move.
        require(pivot in black or move == pivot, "maker-policy", f"turn {turn} does not play its pivot")
        check_move(move, "Black", turn)
        black.add(move)
        witness = winning_witness(frozenset(black))
        if witness is not None:
            require(turn == len(route), "early-win", f"Black had already won on move {turn}")
            require("breaker_reply" not in step and "next_hint" not in step,
                    "after-win", "terminal turn includes play after the win")
            break
        require(turn < len(route), "incomplete-win", "route ends without a Snaky placement")
        reply = _point(step.get("breaker_reply"), "breaker_reply")
        check_move(reply, "White", turn)
        local = next((point for point in card.support if _apply(matrix, point) == reply), None)
        claimed_local = step.get("local_breaker_reply")
        require(claimed_local == (list(local) if local is not None else None),
                "reply-class", f"turn {turn} has the wrong local reply class")
        if local is None:
            hint = card.outside
            outside_replies += 1
        else:
            hint = next((hint for point, hint in card.responses if point == local), None)
        require(hint is not None, "missing-source-hint", f"turn {turn} lacks a selected source hint")
        expected = {"child": hint.card, "orientation": hint.orientation,
                    "translation": [hint.dx, hint.dy]}
        require(step.get("next_hint") == expected, "source-hint",
                f"turn {turn} next_hint differs from the certificate")
        require(0 <= hint.card < len(certificate.cards), "reference", "selected child does not exist")
        child = certificate.cards[hint.card]
        require(1 <= child.height < card.height, "height-descent", f"turn {turn} has no height descent")
        next_matrix = _compose(matrix, hint)
        child_required = frozenset(_apply(next_matrix, point) for point in child.required)
        child_region = frozenset(_apply(next_matrix, point) for point in child.support)
        require(child_required <= (required | {pivot}), "requirements",
                f"turn {turn} selected hint needs ownership outside the source card")
        require(child_region <= region - {reply}, "support",
                f"turn {turn} selected hint escapes White-free support")
        white.add(reply)
        index, matrix = hint.card, next_matrix

    detail = outcome.get("detail")
    require(isinstance(detail, dict), "transcript-format", "final detail object required")
    require(detail.get("maker_moves") == len(route), "final-claim", "wrong final Black move count")
    require(_points(detail.get("maker"), "final maker") == black,
            "final-claim", "wrong final Black stones")
    require(_points(detail.get("breaker"), "final breaker") == white,
            "final-claim", "wrong final White stones")
    claimed_win = _points(detail.get("winning_placement"), "winning_placement")
    require(len(claimed_win) == 6 and claimed_win <= black
            and normalize(claimed_win) in SHAPE_ORIENTATIONS,
            "winning-claim", "reported final placement is not a Black-owned Snaky")
    return {
        "status": "verified",
        "scope": "one concrete transcript and its selected certificate hints",
        "geometry": "integer plane" if plane else f"{certificate.rows}x{certificate.cols} finite board",
        "black_moves": len(black),
        "white_moves": len(white),
        "first_snaky_on_black_move": len(route),
        "selected_hint_checks": len(route) - 1,
        "outside_support_replies": outside_replies,
        "finite_board_legal": not off_board,
        "off_board_moves": off_board,
        "cards": card_indices,
        "winning_placement": [list(point) for point in witness],
        "whole_strategy_checked_by_this_run": False,
        "game_lower_bound_claimed": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("transcript_report", type=Path)
    parser.add_argument("--outcome", default="legal_twenty_move_route")
    parser.add_argument("--plane", action="store_true", help="allow moves outside the named finite board")
    args = parser.parse_args(argv)
    try:
        certificate_data = args.certificate.read_bytes()
        report_data = args.transcript_report.read_bytes()
        certificate = parse_text(certificate_data.decode("ascii"))
        report = json.loads(report_data)
        outcome = report["replay"]["representative_outcomes"][args.outcome]
        result = verify_transcript(certificate, outcome, plane=args.plane)
        result.update({
            "certificate_sha256": hashlib.sha256(certificate_data).hexdigest(),
            "transcript_report_sha256": hashlib.sha256(report_data).hexdigest(),
            "outcome": args.outcome,
            "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "card_verifier_sha256": hashlib.sha256(Path(__file__).with_name("verify_cards.py").read_bytes()).hexdigest(),
        })
    except (InvalidCertificate, OSError, UnicodeError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}, indent=2))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
