#!/usr/bin/env python3
"""Transcribe the accepted C30 table for the generic Lean selected-game checker.

Outside physical replies with identical internal state are shared. The Lean
soundness theorem, rather than this untrusted transformation, proves the lift
back to all physical replies and all nine original stones of each color.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
BOARD = FORMAL.parent / "board_size"
REPORT = BOARD / "verification/c30-seventeen-guard-obstruction-01.json"
REPORT_SHA = "f9a2efdd84acb4d6bec167b925683ec29390c9aad6d8b985293a7415a9e72a51"
CHECKER = BOARD / "verification/c30_seventeen_guard_obstruction.py"
CHECKER_SHA = "7d0fb00de7b89d336432257d65de3667b7aa56dea2e0be497d39fb66349e6769"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree(items, leaf):
    if len(items) == 1:
        return leaf(items[0])
    mid = len(items) // 2
    return f"(.node {items[mid]} {tree(items[:mid], leaf)} {tree(items[mid:], leaf)})"


def glue(items):
    if len(items) == 1:
        return f"row{items[0]}_ok"
    mid = len(items) // 2
    return f"⟨{glue(items[:mid])}, {glue(items[mid:])}⟩"


def action_text(action):
    return f".{action[0]} {action[1]}"


def collect(report):
    replay = report["replay"]
    original = replay["rows"]
    guards = report["named_guards"]
    support = sorted(set().union(*map(set, guards.values())))
    core = set(support)
    m0, b0 = replay["initial_maker"], replay["initial_breaker"]
    if len(guards) != 17 or len(core) != 22 or (set(m0) | set(b0)) & core:
        raise ValueError("changed selected domain or initial colors")
    if len(original) != 460 or replay["root"] != 0:
        raise ValueError("changed accepted finite table")
    rows, known = [], {}

    def walk(index, M, B):
        old = original[index]
        if (old["node"] != index or set(old["maker_before"]) & core != set(M)
                or set(old["breaker_before"]) & core != set(B)
                or not set(m0) <= set(old["maker_before"])
                or not set(b0) <= set(old["breaker_before"])):
            raise ValueError("source row lost old colors or internal history")
        key = M, B, old["maker"]
        fresh = key not in known
        if fresh:
            rowid = len(rows)
            known[key] = rowid
            rows.append(None)
        else:
            rowid = known[key]
        # There are no immediate leaves in this particular accepted table.
        if "terminal" in old:
            raise ValueError("unexpected immediate leaf; extend transcription explicitly")
        entries, outside = [], []
        for branch in old["replies"]:
            w = branch["reply"]
            if "completion" in branch:
                action = "finish", branch["completion"]
            else:
                childB = (w, *B) if w in core else B
                action = "next", walk(branch["child"], (old["maker"], *M), childB)
            if w in core:
                entries.append((w, action))
            else:
                outside.append(action)
        if not outside or len(set(outside)) != 1:
            raise ValueError("outside histories do not have one internal continuation")
        expected = sorted(core - set(M) - set(B) - {old["maker"]})
        if [w for w, _ in entries] != expected:
            raise ValueError("missing or duplicated internal reply")
        value = dict(maker=list(M), breaker=list(B), height=10-len(M),
                     move=old["maker"], outside=outside[0], replies=entries)
        if fresh:
            rows[rowid] = value
        elif rows[rowid] != value:
            raise ValueError("shared internal histories disagree")
        return rowid

    root = walk(0, (), ())
    if root != 0 or len(rows) != 106 or any(row is None for row in rows):
        raise ValueError(f"unexpected compressed table size: root={root}, rows={len(rows)}, missing={sum(row is None for row in rows)}")
    return guards, support, m0, b0, rows


def sources():
    if sha(REPORT) != REPORT_SHA or sha(CHECKER) != CHECKER_SHA:
        raise ValueError("changed accepted source or report")
    report = json.loads(REPORT.read_text())
    guards, support, m0, b0, rows = collect(report)
    labels = ["C1", "C2", "C3", "C4", "C5", "p", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"]
    header = "-- Generated from the pinned accepted finite table; Lean checks every row.\n"
    definitions = []
    for i, row in enumerate(rows):
        replies = ", ".join(f"({w}, {action_text(a)})" for w, a in row["replies"])
        definitions.append(f"def row{i} : Row := ⟨{row['maker']}, {row['breaker']}, {row['height']}, {row['move']}, {action_text(row['outside'])}, [{replies}]⟩")
    ids = list(range(len(rows)))
    data = header + f"""import Snaky.SelectedAttack

namespace Snaky.C30Selected
open SelectedAttack

/-- These 17 selected guards are not the full Snaky target family. -/
def guards : List (List Nat) := {[guards[label] for label in labels]}
def core : List Nat := {support}
def initialMaker : List Nat := {m0}
def initialBreaker : List Nat := {b0}

{chr(10).join(definitions)}

def tree : Tree := {tree(ids, lambda i: f'(.leaf {i} row{i})')}
def getRow : Nat → Option Row := tree.get

end Snaky.C30Selected
"""
    output = {"Snaky/C30Data.lean": data}
    chunks = [ids[start:start+4] for start in range(0, len(rows), 4)]
    for index, chunk in enumerate(chunks):
        proofs = "\n\n".join(
            f"set_option maxHeartbeats 0 in\ntheorem row{i}_ok : Valid guards core getRow row{i} := by\n  decide +kernel"
            for i in chunk)
        output[f"Snaky/C30Check{index:02}.lean"] = header + f"""import Snaky.C30Data

namespace Snaky.C30Selected
open SelectedAttack
set_option maxRecDepth 4096

{proofs}

end Snaky.C30Selected
"""
    imports = "".join(f"import Snaky.C30Check{i:02}\n" for i in range(len(chunks)))
    output["Snaky/C30Checks.lean"] = header + imports + f"""
namespace Snaky.C30Selected
open SelectedAttack

theorem tree_ok : tree.All (Valid guards core getRow) := {glue(ids)}

end Snaky.C30Selected
"""
    return output, dict(input_report_sha256=REPORT_SHA, input_checker_sha256=CHECKER_SHA,
        selected_guards=17, selected_domain=22, physical_rows=460, internal_rows=len(rows),
        full_physical_board_cells=100, initial_stones_per_color=9, height=10,
        physical_snaky_win_claim=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output, provenance = sources()
    for name, text in output.items():
        path = FORMAL / name
        if args.check:
            if path.read_text() != text:
                raise ValueError("generated file differs: " + name)
        else:
            path.write_text(text)
    provenance.update(status="transcribed_not_kernel_checked", generator_sha256=sha(Path(__file__)),
        generated_sha256={name: hashlib.sha256(text.encode()).hexdigest() for name, text in output.items()})
    if not args.check:
        (FORMAL / "C30-provenance.json").write_text(json.dumps(provenance, indent=2, sort_keys=True)+"\n")
    print(json.dumps(provenance, sort_keys=True))


if __name__ == "__main__":
    main()
