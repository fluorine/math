"""Positive and negative controls for exhaustive one-cell completions."""

import unittest

from verify_cards import InvalidCertificate, SHAPE
from verify_one_move import one_move_completions


class OneMoveTests(unittest.TestCase):
    def test_five_owned_cells_have_a_completion(self):
        result = one_move_completions(frozenset(SHAPE[:-1]), frozenset())
        self.assertIn(list(SHAPE[-1]), result["legal_completion_moves"])
        self.assertFalse(result["cannot_win_on_next_move"])

    def test_white_blocks_completion(self):
        result = one_move_completions(frozenset(SHAPE[:-1]), frozenset({SHAPE[-1]}))
        self.assertTrue(result["cannot_win_on_next_move"])
        self.assertEqual(result["legal_completion_moves"], [])
        self.assertGreater(result["blocked_by_black_overlap"].get(5, 0), 0)

    def test_four_cells_cannot_finish_six_cell_shape(self):
        result = one_move_completions(frozenset(SHAPE[:4]), frozenset())
        self.assertTrue(result["cannot_win_on_next_move"])

    def test_already_won_is_not_impossibility(self):
        result = one_move_completions(frozenset(SHAPE), frozenset())
        self.assertGreater(result["already_won_placements"], 0)
        self.assertFalse(result["cannot_win_on_next_move"])

    def test_disjoint_position_and_illegal_overlap(self):
        self.assertTrue(one_move_completions(frozenset(), frozenset())["cannot_win_on_next_move"])
        with self.assertRaises(InvalidCertificate):
            one_move_completions(frozenset(SHAPE), frozenset({SHAPE[0]}))


if __name__ == "__main__":
    unittest.main()
