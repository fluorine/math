"""Focused replay controls; this synthetic line alone is not a strategy proof."""

from copy import deepcopy
import unittest

from verify_cards import Card, Certificate, Hint, InvalidCertificate, SHAPE
from verify_transcript import verify_transcript


def example_line():
    cards = []
    route = []
    white = []
    for index, pivot in enumerate(SHAPE):
        hint = Hint(index + 1, 0) if index < 5 else None
        cards.append(Card(6 - index, pivot, SHAPE[:index], SHAPE, hint, ()))
        step = {"maker_turn": index + 1, "card": index, "height": 6 - index,
                "transform": [1, 0, 0, 1, 0, 0], "maker_move": list(pivot),
                "required_maker": [list(p) for p in SHAPE[:index]], "forgotten_maker": []}
        if index < 5:
            reply = [9, index]
            white.append(reply)
            step.update({"breaker_reply": reply, "local_breaker_reply": None,
                         "next_hint": {"child": index + 1, "orientation": 0, "translation": [0, 0]}})
        route.append(step)
    outcome = {"route": route, "detail": {"maker": [list(p) for p in SHAPE], "breaker": white,
                                          "winning_placement": [list(p) for p in SHAPE], "maker_moves": 6}}
    return Certificate(10, 10, Hint(0, 0), tuple(cards)), outcome


class TranscriptVerifierTests(unittest.TestCase):
    def assert_rejected(self, code, certificate, outcome):
        with self.assertRaises(InvalidCertificate) as raised:
            verify_transcript(certificate, outcome)
        self.assertEqual(raised.exception.code, code)

    def test_valid_line(self):
        certificate, outcome = example_line()
        result = verify_transcript(certificate, outcome)
        self.assertEqual(result["first_snaky_on_black_move"], 6)
        self.assertEqual(result["selected_hint_checks"], 5)
        self.assertTrue(result["finite_board_legal"])
        self.assertFalse(result["whole_strategy_checked_by_this_run"])

    def test_plane_is_not_finite_board(self):
        certificate, outcome = example_line()
        outcome["route"][0]["breaker_reply"] = [-1, 0]
        outcome["detail"]["breaker"][0] = [-1, 0]
        self.assert_rejected("off-board", certificate, outcome)
        result = verify_transcript(certificate, outcome, plane=True)
        self.assertFalse(result["finite_board_legal"])

    def test_repeated_white_move(self):
        certificate, outcome = example_line()
        outcome["route"][1]["breaker_reply"] = [9, 0]
        self.assert_rejected("occupied-move", certificate, outcome)

    def test_wrong_transform_or_hint(self):
        certificate, outcome = example_line()
        changed = deepcopy(outcome)
        changed["route"][1]["transform"][4] = 1
        self.assert_rejected("route-transform", certificate, changed)
        outcome["route"][0]["next_hint"]["child"] = 99
        self.assert_rejected("source-hint", certificate, outcome)

    def test_premature_end_or_continuation_after_win(self):
        certificate, outcome = example_line()
        changed = deepcopy(outcome)
        changed["route"].pop()
        self.assert_rejected("incomplete-win", certificate, changed)
        outcome["route"].append({})
        self.assert_rejected("early-win", certificate, outcome)

    def test_wrong_ownership_claim(self):
        certificate, outcome = example_line()
        outcome["route"][1]["required_maker"] = []
        self.assert_rejected("ownership-claim", certificate, outcome)

    def test_false_final_witness(self):
        certificate, outcome = example_line()
        outcome["detail"]["winning_placement"] = [[x, 0] for x in range(6)]
        self.assert_rejected("winning-claim", certificate, outcome)


if __name__ == "__main__":
    unittest.main()
