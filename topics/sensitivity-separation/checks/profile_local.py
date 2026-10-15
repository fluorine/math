#!/usr/bin/env python3
"""Bounded regression checks for proofs/PROFILE.md; standard library only.

The state of a child is 0=(gate,target)=(0,0), 1=(1,0), or 2=(1,1).
This checks local candidate geometry, not global realizability of profile
maxima by one recursive input and not an explicit tournament generator.
"""

from dataclasses import dataclass
from itertools import combinations, product
import json


@dataclass(frozen=True)
class Model:
    rows: tuple[tuple[int, ...], ...]
    edges: tuple[tuple[int, int, int], ...]


@dataclass(frozen=True)
class Candidates:
    targets: tuple[int, ...]
    gates: tuple[int, ...]
    ordinary_targets: tuple[int, ...]
    ordinary_gates: tuple[int, ...]
    missing: dict[int, int]


def coherent(edges, vertices):
    """Labels agree at the HEAD; sources impose no condition."""
    vertices = set(vertices)
    incoming = {}
    for tail, head, label in edges:
        if tail in vertices and head in vertices:
            if head in incoming and incoming[head] != label:
                return False
            incoming[head] = label
    return True


def coherent_capacity(edges, n):
    for size in range(n, -1, -1):
        if any(coherent(edges, subset) for subset in combinations(range(n), size)):
            return size
    raise AssertionError("The empty set is coherent")


def candidates(model):
    targets, gates, ordinary_targets, ordinary_gates = [], [], [], []
    missing = {}
    for vertex, row in enumerate(model.rows):
        target_failures = [c for c, state in enumerate(row) if state != 2]
        gate_failures = [
            (head, label)
            for tail, head, label in model.edges
            if tail == vertex and model.rows[head][label] != 0
        ]
        if not target_failures and not gate_failures:
            return None  # The parent is one, outside this lemma's premise.
        if len(target_failures) == 1 and not gate_failures:
            targets.append(vertex)
            missing[vertex] = target_failures[0]
            if row[target_failures[0]] == 1:
                ordinary_targets.append(vertex)
        if not target_failures and len(gate_failures) == 1:
            gates.append(vertex)
            head, label = gate_failures[0]
            if model.rows[head][label] == 1:
                ordinary_gates.append(vertex)
    return Candidates(tuple(targets), tuple(gates), tuple(ordinary_targets),
                      tuple(ordinary_gates), missing)


def envelopes(capacity, A, B, C, D):
    """The general-capacity version of the six/five branches."""
    h = capacity
    ordinary = max(A + (h - 1) * C,
                   A + (h - 2) * C + B,
                   h * C + D,
                   (h - 2) * C + B + D,
                   (h - 1) * C + 2 * D,
                   (h - 3) * C + 3 * D)
    joint = max(A + (h - 1) * C,
                A + (h - 2) * C + D,
                h * C + D,
                (h - 1) * C + 2 * D,
                (h - 3) * C + 3 * D)
    return ordinary, joint


WEIGHTS = ((1, 1, 0, 0), (1, 1, 1, 1), (7, 11, 3, 5),
           (3, 9, 2, 7), (9, 3, 6, 1))


def check_candidate_bounds(model, cand, capacity):
    T, G = set(cand.targets), set(cand.gates)
    ordinary_t, ordinary_g = len(cand.ordinary_targets), len(cand.ordinary_gates)
    t, g = len(T), len(G)
    assert not T.intersection(G)
    assert coherent(model.edges, T)
    assert t <= capacity and g <= 3
    assert ordinary_t <= 1 and ordinary_g <= 1
    for tail, head, label in model.edges:
        assert not (tail in T and head in G)
        if tail in T and head in T:
            assert label == cand.missing[head]
            assert head not in cand.ordinary_targets
    if g >= 2:
        assert not ordinary_t
    if g == 0:
        assert t <= capacity
    elif g == 1:
        if ordinary_t or ordinary_g:
            assert t + 1 <= capacity
            assert coherent(model.edges, T.union(G))
        else:
            assert t <= capacity
    elif g == 2:
        if ordinary_g:
            assert t + 2 <= capacity
            assert coherent(model.edges, T.union(G))
        else:
            assert t + 1 <= capacity
    else:
        assert not ordinary_g
        assert t + 3 <= capacity
        assert coherent(model.edges, T.union(G))
        for vertex in G:
            assert sum(tail == vertex and head in G
                       for tail, head, _ in model.edges) == 1
    for A, B, C, D in WEIGHTS:
        assert C <= A and D <= B
        target_cost = ordinary_t * A + (t - ordinary_t) * C
        ordinary_cost = target_cost + ordinary_g * B + (g - ordinary_g) * D
        joint_cost = target_cost + g * D
        bound, joint_bound = envelopes(capacity, A, B, C, D)
        assert ordinary_cost <= bound
        assert joint_cost <= joint_bound


def exhaustive_three_vertices():
    pairs = tuple(combinations(range(3), 2))
    configurations = zero_inputs = max_gates = 0
    for choices in product(range(4), repeat=len(pairs)):
        edges = tuple((i, j, choice % 2) if choice < 2 else
                      (j, i, choice % 2)
                      for (i, j), choice in zip(pairs, choices))
        capacity = coherent_capacity(edges, 3)
        for flat in product(range(3), repeat=6):
            model = Model(tuple(tuple(flat[2 * i:2 * i + 2]) for i in range(3)), edges)
            configurations += 1
            cand = candidates(model)
            if cand is None:
                continue
            zero_inputs += 1
            max_gates = max(max_gates, len(cand.gates))
            check_candidate_bounds(model, cand, capacity)
    assert configurations == 46656
    assert max_gates == 3
    return configurations, zero_inputs, max_gates


def template(target_count, gate_count, ordinary_target=False,
             bad_target_label=False, external_ordinary_gate=False):
    T = tuple(range(target_count))
    G = tuple(range(target_count, target_count + gate_count))
    rows = [(0, 2) for _ in T] + [(2, 2) for _ in G]
    if ordinary_target:
        rows[0] = (1, 2)
    edges = [(i, j, 0) for i, j in combinations(T, 2)]
    if gate_count == 2:
        edges.append((G[0], G[1], 0))
    elif gate_count == 3:
        edges.extend((G[i], G[(i + 1) % 3], 0) for i in range(3))
    edges.extend((gate, target, int(bad_target_label and gate == G[-1]
                                   and target == T[-1]))
                 for gate in G for target in T)
    if external_ordinary_gate:
        external = len(rows)
        rows.append((1, 0))
        edges.extend((vertex, external, 0 if vertex == G[-1] else 1)
                     for vertex in range(external))
    return Model(tuple(rows), tuple(edges))


def exact_templates():
    examples = (
        ("no_gates", template(15, 0, ordinary_target=True), (1, 14, 0, 0)),
        ("one_ordinary_gate", template(14, 1, ordinary_target=True), (1, 13, 1, 0)),
        ("one_joint_gate", template(15, 1, bad_target_label=True), (0, 15, 0, 1)),
        ("two_gates_ordinary_sink", template(13, 2, external_ordinary_gate=True), (0, 13, 1, 1)),
        ("two_joint_gates", template(14, 2, bad_target_label=True), (0, 14, 0, 2)),
        ("three_joint_gates", template(12, 3), (0, 12, 0, 3)),
    )
    verified = []
    for name, model, expected in examples:
        n = len(model.rows)
        assert len(model.edges) == n * (n - 1) // 2
        assert len({frozenset((i, j)) for i, j, _ in model.edges}) == len(model.edges)
        cand = candidates(model)
        assert cand is not None
        actual = (len(cand.ordinary_targets),
                  len(cand.targets) - len(cand.ordinary_targets),
                  len(cand.ordinary_gates),
                  len(cand.gates) - len(cand.ordinary_gates))
        assert actual == expected, (name, actual, expected)
        # At most sixteen local vertices: only the entire sixteen-set
        # can violate the no-coherent-sixteen contract.
        assert n <= 16
        if n == 16:
            assert not coherent(model.edges, range(n))
        else:
            assert coherent(model.edges, range(n))
        assert any(coherent(model.edges, subset)
                   for subset in combinations(range(n), 15))
        check_candidate_bounds(model, cand, 15)
        verified.append(name)
    return verified


def counterexamples():
    tail_coherent = ((0, 1, 0), (0, 2, 0), (1, 2, 1))
    head_coherent = ((0, 1, 0), (0, 2, 1), (1, 2, 1))
    assert not coherent(tail_coherent, range(3))
    assert coherent(head_coherent, range(3))
    assert len({label for tail, _, label in head_coherent if tail == 0}) == 2

    # One ordinary source target plus a joint G->source gate still has a
    # coherent union: the source head label must be reassigned to 1.
    source_reassignment = template(1, 1, ordinary_target=True, bad_target_label=True)
    source_candidates = candidates(source_reassignment)
    assert source_candidates is not None
    assert len(source_candidates.ordinary_targets) == 1
    assert len(source_candidates.ordinary_gates) == 0
    assert coherent(source_reassignment.edges, range(2))

    # Three directed-cycle gates can give three distinct successful flips.
    # Every nested child predicate here is the identical single input bit;
    # each row has two distinct children. This is a generic nested model.
    def cycle_parent(bits):
        return any(bits[2 * i] and bits[2 * i + 1]
                   and not bits[2 * ((i + 1) % 3)] for i in range(3))

    bits = [1] * 6
    assert not cycle_parent(bits)
    successful = []
    for coordinate in range(6):
        flipped = bits.copy()
        flipped[coordinate] ^= 1
        if cycle_parent(flipped):
            successful.append(coordinate)
    assert successful == [0, 2, 4]
    return ["head_not_tail", "source_head_reassignment", "three_distinct_gate_repairs"]


def main():
    configurations, zeros, max_gates = exhaustive_three_vertices()
    templates = exact_templates()
    obstructions = counterexamples()
    print(json.dumps({
        "status": "PASS",
        "exhaustive_configurations": configurations,
        "zero_inputs_checked": zeros,
        "maximum_gate_candidates": max_gates,
        "exact_counting_templates": templates,
        "counterexamples_checked": obstructions,
        "scope": "local combinatorial regression, not a substitute for the proof",
    }, indent=2))


if __name__ == "__main__":
    main()
