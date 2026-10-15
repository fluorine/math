"""Small regressions for geometric matching and certificate reindexing."""
import time
import unittest

from analyze_routes import Card, Hint, ORIENTS, SNAKY, transform
from history_closure import Catalog, append_catalog
from prune_certificate import prune


def mask(points, width):
    return sum(1 << (y * width + x) for x, y in points)


class CatalogTests(unittest.TestCase):
    def test_all_orientations_match_and_blocked_support_rejects(self):
        card = Card(1, SNAKY[-1], frozenset(SNAKY[:-1]), frozenset(SNAKY), None, [])
        catalog = Catalog([card], 11, 11, time.monotonic() + 30)
        board = (1 << 121) - 1
        for orient in ORIENTS:
            g = (*orient, 5, 5)
            maker = frozenset(transform(g, q) for q in card.required)
            result = catalog.find(mask(maker, 11), board, 1)
            self.assertIsNotNone(result)
            actual_required = {transform(result.xf, q) for q in card.required}
            actual_support = {transform(result.xf, q) for q in card.support}
            self.assertTrue(actual_required <= maker)
            self.assertTrue(all(0 <= x < 11 and 0 <= y < 11 for x, y in actual_support))
            # Six distinct support cells cannot fit in only five safe cells.
            self.assertIsNone(catalog.find(mask(maker, 11), mask(maker, 11), 1))

    def test_bit_adjacency_cannot_wrap_a_board_row(self):
        card = Card(1, (2, 0), frozenset({(0, 0), (1, 0)}),
                    frozenset({(0, 0), (1, 0), (2, 0)}), None, [])
        catalog = Catalog([card], 7, 7, time.monotonic() + 30)
        maker = mask({(6, 0), (0, 1)}, 7)
        self.assertIsNone(catalog.find(maker, (1 << 49) - 1, 1))

    def test_catalog_append_remaps_every_hint_and_preserves_input(self):
        terminal = Card(1, (0, 0), frozenset(), frozenset({(0, 0)}), None, [])
        h = Hint(0, 7, 2, 3)
        root = Card(2, (1, 0), frozenset(), frozenset({(0, 0), (1, 0)}),
                    h, [((0, 0), h)])
        cards = [terminal, terminal]
        append_catalog(cards, [terminal, root])
        self.assertEqual(cards[3].outside, Hint(2, 7, 2, 3))
        self.assertEqual(cards[3].replies, [((0, 0), Hint(2, 7, 2, 3))])
        self.assertEqual(root.outside.child, 0)

    def test_prune_handles_forward_source_ids_and_drops_unreachable_card(self):
        leaf = Card(1, (0, 0), frozenset(), frozenset({(0, 0)}), None, [])
        h = Hint(2, 4, 5, 6)
        root = Card(2, (1, 0), frozenset(), frozenset({(0, 0), (1, 0)}),
                    h, [((0, 0), h)])
        cards, remapped, order = prune([root, leaf, leaf], Hint(0, 3, 7, 8))
        self.assertEqual(order, [2, 0])
        self.assertEqual(remapped, Hint(1, 3, 7, 8))
        self.assertEqual(cards[1].outside, Hint(0, 4, 5, 6))
        self.assertEqual(cards[1].replies, [((0, 0), Hint(0, 4, 5, 6))])


if __name__ == "__main__":
    unittest.main()
