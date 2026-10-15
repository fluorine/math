"""Discover and exactly check a hidden-schedule witness for EXTENSION.md.

The LP is only a constructive search subclass. A feasible, exactly checked
table still needs the filtered-law and ordinary-call bridges in Lean. An
infeasible LP does not exclude the broader decision class in EXTENSION.md.

Run with the project's .venv Python and one compute process. This script sets
thread limits before importing NumPy/SciPy. All final equalities are checked
with fractions.Fraction against the original integer rows.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from math import comb, gcd, lcm
import os
from pathlib import Path
import re
import time

for _key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS",
             "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_key] = "1"

ROOT = Path(__file__).resolve().parent.parent
SCHEDULES = tuple(itertools.product(range(2), repeat=6))
SIGNALS = tuple(itertools.product(range(4), repeat=3))
TARGET = ((12, 12, 36, 4), (2, 30, 30, 2), (1, 46, 1, 16))
WINDOWS = tuple(tuple(sum(a[i + 1:i + 4]) for i in range(3))
                for a in SCHEDULES)


def allowed(a: int, y: int) -> bool:
    """Extreme conditional means force the corresponding count pointwise.

    For each fixing history, all terms p*W are nonnegative when Y=0;
    all terms p*(W-3) are nonpositive when Y=3. Their sum is zero.
    Therefore a positive-weight state must have W=Y in either extreme.
    """
    return all(value not in (0, 3) or WINDOWS[a][i] == value
               for i, value in enumerate(SIGNALS[y]))


def make_system():
    states = tuple((a, y) for a in range(64) for y in range(64)
                   if allowed(a, y))
    rows: list[tuple[str, dict[int, int], Fraction]] = []

    # Every prefix-count atom, including the normalization at prefix length 0.
    for length in range(7):
        for count in range(length + 1):
            values = {col: 1 for col, (a, _) in enumerate(states)
                      if sum(SCHEDULES[a][:length]) == count}
            rows.append((f"prefix:{length}:{count}", values,
                         Fraction(comb(length, count), 2 ** length)))

    for i in range(3):
        for value in range(4):
            values = {col: 1 for col, (_, y) in enumerate(states)
                      if SIGNALS[y][i] == value}
            rows.append((f"signal:{i}:{value}", values,
                         Fraction(TARGET[i][value], 64)))

    # Keep all histories, including empty and zero-probability histories.
    for i in range(3):
        length = i + 1
        keys = tuple(itertools.product(
            itertools.product(range(2), repeat=length),
            itertools.product(range(4), repeat=length)))
        buckets = {key: {} for key in keys}
        for col, (a, y) in enumerate(states):
            coefficient = WINDOWS[a][i] - SIGNALS[y][i]
            if coefficient:
                key = (SCHEDULES[a][:length], SIGNALS[y][:length])
                buckets[key][col] = coefficient
        for (activity, signal), values in buckets.items():
            activity_text = "".join(map(str, activity))
            signal_text = "".join(map(str, signal))
            rows.append((f"history:{i}:{activity_text}:{signal_text}",
                         values, Fraction(0)))
    return states, rows


def verify_exact(weights, states, rows):
    assert len(weights) == len(states)
    assert all(weight >= 0 for weight in weights), "negative exact weight"
    assert sum(weights, Fraction(0)) == 1, "normalization failed"
    failures = []
    for name, coefficients, rhs in rows:
        value = sum((coefficient * weights[col]
                     for col, coefficient in coefficients.items()), Fraction(0))
        if value != rhs:
            failures.append((name, str(value), str(rhs)))
    if failures:
        raise ValueError(f"exact verification failed: {failures[:8]}")

    # Check all original 4096-state history equations independently, directly
    # from the sparse support rather than from the LP coefficient matrix.
    support = [(SCHEDULES[a], SIGNALS[y], weights[col])
               for col, (a, y) in enumerate(states) if weights[col]]
    history_count = 0
    for i in range(3):
        length = i + 1
        for past_a in itertools.product(range(2), repeat=length):
            for past_y in itertools.product(range(4), repeat=length):
                residual = sum((p * (sum(a[i + 1:i + 4]) - y[i])
                                for a, y, p in support
                                if a[:length] == past_a and y[:length] == past_y),
                               Fraction(0))
                assert residual == 0, (i, past_a, past_y, residual)
                history_count += 1
    return {"all_rows": len(rows), "prefix_rows": 28, "signal_rows": 12,
            "history_rows": history_count,
            "normalization": "1", "all_weights_nonnegative": True,
            "exact_residual": "0", "arithmetic": "fractions.Fraction"}


def reconstruct(values, states, rows, max_denominator):
    # Candidate rational reconstruction is never accepted before exact checks.
    guesses = [Fraction(float(value)).limit_denominator(max_denominator)
               if abs(value) > 1e-10 else Fraction(0) for value in values]
    verify_exact(guesses, states, rows)
    return guesses


def save_certificate(path, weights, states, rows, metadata):
    exact_check = verify_exact(weights, states, rows)
    denominator = lcm(*(p.denominator for p in weights))
    entries = [{"schedule_index": a, "schedule": "".join(map(str, SCHEDULES[a])),
                "signal_index": y, "signals": list(SIGNALS[y]),
                "numerator": int(p * denominator)}
               for (a, y), p in zip(states, weights) if p]
    common = gcd(denominator, *(entry["numerator"] for entry in entries))
    denominator //= common
    for entry in entries:
        entry["numerator"] //= common
    data = {
        "schema": "hidden-schedule-witness-v1", "epsilon": "0",
        "scope": "constructive hidden-schedule subclass; not a Lean theorem",
        "schedules": "lexicographic six-bit strings, index 0 through 63",
        "signals": "lexicographic base-four triples, index 0 through 63",
        "original_state_count": 4096, "allowed_state_count": len(states),
        "pruning": "Y_i in {0,3} forces W_i=Y_i at positive-weight states",
        "denominator": denominator, "support_size": len(entries),
        "target_signal_numerators": [list(row) for row in TARGET],
        "target_signal_denominator": 64, "support": entries,
        "exact_check": exact_check, "discovery": metadata,
    }
    path.write_text(json.dumps(data, indent=2) + "\n")
    return data


def check_lean_literals(data):
    source = ROOT / "formal/VixOverlap/HiddenData.lean"
    text = source.read_text()
    expected = {
        "scheduleIndex": [item["schedule_index"] for item in data["support"]],
        "signalCode": [item["signal_index"] for item in data["support"]],
        "numerator": [item["numerator"] for item in data["support"]],
    }
    assert data["denominator"] == 1024
    assert data["support_size"] == len(data["support"]) == 39
    assert re.search(r"abbrev\s+Atom\s*:=\s*Fin\s+39\b", text)
    for name, values in expected.items():
        match = re.search(r"def\s+" + name + r"\s*:\s*Atom\s*→\s*ℕ\s*:=\s*!\[(.*?)\]",
                          text, re.DOTALL)
        assert match, f"missing literal definition {name}"
        actual = [int(value.strip()) for value in match.group(1).split(",")]
        assert actual == values, f"Lean literal mismatch in {name}"
    assert re.search(r"def\s+weight\s*\(a\s*:\s*Atom\)\s*:\s*ℝ\s*:=\s*numerator\s+a\s*/\s*1024\b", text)
    return {"file": str(source), "literal_vectors": 3, "entries_per_vector": 39,
            "denominator": 1024, "match": True}


def check_saved(path, states, rows, check_lean):
    data = json.loads(path.read_text())
    index = {state: col for col, state in enumerate(states)}
    weights = [Fraction(0) for _ in states]
    for item in data["support"]:
        state = item["schedule_index"], item["signal_index"]
        assert state in index, "certificate contains pruned state"
        assert item["schedule"] == "".join(map(str, SCHEDULES[state[0]]))
        assert item["signals"] == list(SIGNALS[state[1]])
        weights[index[state]] += Fraction(item["numerator"], data["denominator"])
    result = verify_exact(weights, states, rows)
    output = {"certificate": str(path), "verification": result}
    if check_lean:
        output["lean_literals"] = check_lean_literals(data)
    print(json.dumps(output, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempts", type=int, default=1)
    parser.add_argument("--seed", type=int, default=20261015)
    parser.add_argument("--max-denominator", type=int, default=10 ** 9)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "certificates/hidden-witness.json")
    parser.add_argument("--check", type=Path)
    parser.add_argument("--check-lean", action="store_true",
                        help="also compare saved support to HiddenData.lean literals")
    args = parser.parse_args()
    states, rows = make_system()
    if args.check:
        check_saved(args.check, states, rows, args.check_lean)
        return
    if args.check_lean:
        parser.error("--check-lean requires --check")
    # Exact saved-certificate checking requires only the Python standard library.
    import numpy as np
    import scipy
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    sparse_r, sparse_c, sparse_v = [], [], []
    for r, (_, values, _) in enumerate(rows):
        for col, value in values.items():
            sparse_r.append(r); sparse_c.append(col); sparse_v.append(value)
    matrix = coo_matrix((sparse_v, (sparse_r, sparse_c)),
                        shape=(len(rows), len(states))).tocsr()
    rhs = np.array([float(row[2]) for row in rows])
    rng = np.random.default_rng(args.seed)
    print(f"Search: {len(states)}/4096 states, {len(rows)} exact rows", flush=True)
    best_support = len(states) + 1
    records = []
    for attempt in range(args.attempts):
        objective = np.zeros(len(states)) if attempt == 0 else rng.random(len(states))
        started = time.monotonic()
        result = linprog(objective, A_eq=matrix, b_eq=rhs, bounds=(0, None),
                         method="highs-ds", options={"time_limit": 120,
                         "primal_feasibility_tolerance": 1e-9,
                         "dual_feasibility_tolerance": 1e-9})
        metadata = {"attempt": attempt, "seed": args.seed,
                    "scipy_version": scipy.__version__, "solver": "HiGHS dual simplex",
                    "solver_status": int(result.status), "solver_message": result.message,
                    "seconds": time.monotonic() - started}
        records.append(metadata)
        print(json.dumps(metadata), flush=True)
        if not result.success:
            (ROOT / "certificates/hidden-search-status.json").write_text(
                json.dumps({"scope": "numerical subclass search only", "attempts": records},
                           indent=2) + "\n")
            if result.status == 2:
                break
            continue
        try:
            weights = reconstruct(result.x, states, rows, args.max_denominator)
        except ValueError as error:
            print(str(error), flush=True)
            continue
        support_size = sum(p != 0 for p in weights)
        if support_size < best_support:
            data = save_certificate(args.output, weights, states, rows, metadata)
            best_support = support_size
            print(f"EXACT witness: support={support_size}, denominator={data['denominator']}",
                  flush=True)
    if best_support == len(states) + 1:
        raise SystemExit("No exactly verified witness was produced.")


if __name__ == "__main__":
    main()
