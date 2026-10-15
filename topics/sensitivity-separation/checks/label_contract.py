#!/usr/bin/env python3
"""Succinct labels for the exact family-132 head-coherence contract.

The infinite-family guarantee is proved in ../proofs/CONSTRUCTOR.md.
The self-test is bounded finite diagnostic coverage, not the proof.
Python standard library only. No large tournament is materialized.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations, product
import json
from math import isqrt, prod
import time


def digits(index: int, radices: tuple[int, ...]) -> tuple[int, ...]:
    """Mixed-radix digits, most significant first; reject out-of-range input."""
    if index < 0 or any(q < 2 for q in radices):
        raise ValueError("index must be nonnegative and every radix at least two")
    result = [0] * len(radices)
    for u in range(len(radices) - 1, -1, -1):
        index, result[u] = divmod(index, radices[u])
    if index:
        raise ValueError("index exceeds the word capacity")
    return tuple(result)


def word_label(tail: tuple[int, ...], head: tuple[int, ...],
               radices: tuple[int, ...]) -> int:
    """First-difference position plus source digit's rank excluding the head."""
    if len(tail) != len(radices) or len(head) != len(radices):
        raise ValueError("word lengths must equal the radix count")
    if any(q < 2 or not 0 <= a < q or not 0 <= b < q
           for a, b, q in zip(tail, head, radices)):
        raise ValueError("invalid radix or digit")
    offset = 0
    for a, b, q in zip(tail, head, radices):
        if a != b:
            return offset + a - int(a > b)
        offset += q - 1
    raise ValueError("a loop has no edge label")


@dataclass(frozen=True)
class SuccinctTournament:
    """Uniform infinite family: q>=3, M=[13(q-1)]^2, r=13(q-1)."""

    q: int

    def __post_init__(self) -> None:
        if self.q < 3:
            raise ValueError("the proved parameter family requires q >= 3")

    @property
    def r(self) -> int:
        return 13 * (self.q - 1)

    @property
    def M(self) -> int:
        return self.r ** 2

    @property
    def k(self) -> int:
        return 2 * self.M ** 2 + 1

    @property
    def radices(self) -> tuple[int, ...]:
        return (self.q,) * 13

    @classmethod
    def from_M(cls, M: int) -> "SuccinctTournament":
        if M < 0:
            raise ValueError("M must be nonnegative")
        root = isqrt(M)
        if root * root != M or root % 13:
            raise ValueError("M is outside the proved uniform family")
        return cls(1 + root // 13)

    def _validate_pair(self, i: int, j: int) -> None:
        if not 0 <= i < self.k or not 0 <= j < self.k or i == j:
            raise ValueError("distinct vertex indices in [0,k) are required")

    def points_from(self, i: int, j: int) -> bool:
        self._validate_pair(i, j)
        return 1 <= (j - i) % self.k <= self.M ** 2

    def label(self, tail: int, head: int) -> int:
        """Label an actual directed edge; a reversed call is rejected."""
        if not self.points_from(tail, head):
            raise ValueError("the requested directed edge has the other orientation")
        return word_label(digits(tail, self.radices),
                          digits(head, self.radices), self.radices)

    def edge(self, i: int, j: int) -> tuple[int, int, int]:
        """Return tail, head, label for the unordered pair {i,j}."""
        tail, head = (i, j) if self.points_from(i, j) else (j, i)
        return tail, head, self.label(tail, head)


def reference_label(tail: tuple[int, ...], head: tuple[int, ...],
                    radices: tuple[int, ...]) -> int:
    """Independent, deliberately literal implementation for tiny checks."""
    u = next(i for i in range(len(radices)) if tail[i] != head[i])
    allowed_sources = [a for a in range(radices[u]) if a != head[u]]
    return sum(q - 1 for q in radices[:u]) + allowed_sources.index(tail[u])


def head_coherent(vertex_count: int,
                  labelled_edges: list[tuple[int, int, int]]) -> bool:
    """Exact predicate: incoming labels at each head have cardinality <= 1.

    Isolated sources impose no restriction, as required by the source lemma.
    The caller supplies one edge for each unordered vertex pair.
    """
    incoming: list[set[int]] = [set() for _ in range(vertex_count)]
    for _tail, head, label in labelled_edges:
        incoming[head].add(label)
    return all(len(labels) <= 1 for labels in incoming)


def orientation_check(words: tuple[tuple[int, ...], ...],
                      radices: tuple[int, ...], mask: int) -> bool:
    """Decode one tournament, then check the exact incoming-label predicate."""
    labelled_edges = []
    for bit, (i, j) in enumerate(combinations(range(len(words)), 2)):
        tail, head = (j, i) if mask & (1 << bit) else (i, j)
        label = reference_label(words[tail], words[head], radices)
        labelled_edges.append((tail, head, label))
    return head_coherent(len(words), labelled_edges)


def sharp_example(h: int, q: int) -> tuple[tuple[tuple[int, ...], ...],
                                         list[tuple[int, int, int]]]:
    """A coherent h+2 example in an arbitrary orientation, q>=3."""
    if h < 1 or q < 3:
        raise ValueError("sharp example requires h>=1 and q>=3")
    words = [tuple([0] * (h - 1) + [a]) for a in range(3)]
    for u in range(h - 2, -1, -1):
        word = [0] * h
        word[u] = 1
        words.append(tuple(word))
    radices = (q,) * h
    directed = [(0, 1), (1, 2), (2, 0)]
    for head in range(3, len(words)):
        directed.extend((tail, head) for tail in range(head))
    labelled = [(tail, head, reference_label(words[tail], words[head], radices))
                for tail, head in directed]
    return tuple(words), labelled


def self_test() -> dict[str, object]:
    """Bounded checks: 129088 small tournaments, no large search or truth table."""
    started = time.monotonic()

    # Verify fixed-head injectivity and disjoint position palettes directly.
    for radices in ((2, 2), (3, 3), (2, 3, 2)):
        words = tuple(product(*(range(q) for q in radices)))
        for tail in words:
            for head in words:
                if tail != head:
                    actual = word_label(tail, head, radices)
                    assert actual == reference_label(tail, head, radices)
                    assert 0 <= actual < sum(q - 1 for q in radices)
        for i, word in enumerate(words):
            assert digits(i, radices) == word

    # All 64 tournaments on four binary two-digit words: forbidden size four.
    binary_words = tuple(product(range(2), repeat=2))
    for mask in range(1 << 6):
        assert not orientation_check(binary_words, (2, 2), mask)

    # Every five-subset of the nine ternary words, and every orientation:
    # choose(9,5) * 2^choose(5,2) = 129024 nonvacuous checks.
    ternary_words = tuple(product(range(3), repeat=2))
    checked = 64
    for subset in combinations(ternary_words, 5):
        for mask in range(1 << 10):
            assert not orientation_check(subset, (3, 3), mask)
            checked += 1

    # The general bound is sharp, including the actual 15 vs 16 distinction.
    for h in (1, 2, 13):
        words, edges = sharp_example(h, 3)
        assert len(words) == h + 2
        assert len(edges) == len(words) * (len(words) - 1) // 2
        assert head_coherent(len(words), edges)

    # Diagnose the head convention: a transitive triangle whose two incoming
    # labels at the final head differ is NOT coherent, irrespective of sources.
    assert not head_coherent(3, [(0, 1, 0), (0, 2, 0), (1, 2, 1)])
    assert head_coherent(3, [(0, 1, 1), (0, 2, 0), (1, 2, 0)])

    # Check representative parameters using integer arithmetic, including huge q.
    for q in (3, 4, 5, 10, 101, 10**30 + 7):
        generator = SuccinctTournament(q)
        assert generator.M >= 3
        assert generator.r == isqrt(generator.M)
        assert generator.k <= q ** 13
        assert SuccinctTournament.from_M(generator.M) == generator
        k = generator.k
        candidates = (0, 1, generator.M ** 2, generator.M ** 2 + 1, k - 1)
        for i, j in combinations(candidates, 2):
            assert generator.points_from(i, j) != generator.points_from(j, i)
            tail, head, label = generator.edge(i, j)
            assert generator.points_from(tail, head)
            assert 0 <= label < generator.r
            # Do not enumerate the q-digit alphabet in the literal reference
            # implementation when q is enormous.
            if q <= 101:
                assert label == reference_label(digits(tail, generator.radices),
                                                digits(head, generator.radices),
                                                generator.radices)

    # Exhaust regularity for tiny odd orders only; general regularity is proved
    # by the translation-invariant successor interval in CONSTRUCTOR.md.
    for M in (1, 2, 3):
        k = 2 * M * M + 1
        for i in range(k):
            assert sum(1 <= (j - i) % k <= M * M for j in range(k)) == M * M

    for M, radices in ((485, (2,) * 3 + (3,) * 10),
                        (442, (2,) * 5 + (3,) * 8 + (2,))):
        r = isqrt(M - 1) + 1
        assert sum(q - 1 for q in radices) == r
        assert 2 * M * M + 1 <= prod(radices)
        bound = len(radices) + (1 if radices[-1] == 2 else 2)
        assert bound <= 15

    return {
        "status": "passed",
        "small_tournaments_exhausted": checked,
        "sharp_coherent_set_size": 15,
        "smallest_q_in_uniform_family": 3,
        "M_at_q3": SuccinctTournament(3).M,
        "k_at_q3": SuccinctTournament(3).k,
        "large_tournaments_materialized": 0,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "scope": "finite diagnostics; infinite-family proof is CONSTRUCTOR.md",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true",
                        help="run the bounded independent diagnostic checks")
    parser.add_argument("--q", type=int, default=3,
                        help="uniform-family parameter, integer >=3 (default: 3)")
    parser.add_argument("--edge", type=int, nargs=2, metavar=("I", "J"),
                        help="evaluate the orientation and label of one pair")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return
    generator = SuccinctTournament(args.q)
    result: dict[str, object] = {
        "q": generator.q, "M": generator.M, "r": generator.r,
        "k": generator.k, "word_length": 13, "maximum_coherent_size": 15,
    }
    if args.edge is not None:
        tail, head, label = generator.edge(*args.edge)
        result["edge"] = {"tail": tail, "head": head, "label": label}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
