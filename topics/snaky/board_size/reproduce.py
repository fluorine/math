#!/usr/bin/env python3
"""Replay one curated finite audit with explicitly sanitized provenance.

The mathematical checker and all helper code remain byte-for-byte historical.
Only the selected module's PINS values for browser text are replaced, according
to reproduction/inputs.json. That directory contains mathematical text, never
browser DOM. Historical reports are immutable; new outputs and their receipt
must use fresh paths. This program never runs a solver or a research search.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys


BASE = Path(__file__).resolve().parent
MANIFEST = BASE / "reproduction/inputs.json"


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def first_difference(left, right, path="$", limit=240):
    if type(left) is not type(right):
        return dict(path=path, historical=repr(left)[:limit], replay=repr(right)[:limit])
    if isinstance(left, dict):
        if set(left) != set(right):
            return dict(path=path, historical_keys=sorted(left), replay_keys=sorted(right))
        for key in sorted(left):
            found = first_difference(left[key], right[key], path+"."+key)
            if found is not None:
                return found
    elif isinstance(left, list):
        if len(left) != len(right):
            return dict(path=path, historical_length=len(left), replay_length=len(right))
        for index, (old, new) in enumerate(zip(left, right)):
            found = first_difference(old, new, path+f"[{index}]")
            if found is not None:
                return found
    elif left != right:
        return dict(path=path, historical=repr(left)[:limit], replay=repr(right)[:limit])
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", nargs="?")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    require(manifest["schema"] == "snaky-closeout-publication-inputs-v1", "wrong manifest")
    cases = {row["name"]: row for row in manifest["checks"]}
    require(len(cases) == len(manifest["checks"]), "duplicate case")
    if args.list:
        print("\n".join(sorted(cases)))
        return 0
    require(args.case in cases and args.output is not None, "choose a listed case and fresh --output")
    output = args.output.resolve()
    receipt_path = output.with_name(output.name+".publication.json")
    require(not output.exists() and not receipt_path.exists(), "fresh output and receipt required")
    case = cases[args.case]
    records = {row["path"]: row for row in manifest["files"]}
    require(len(records) == len(manifest["files"]), "duplicate file")
    # Verify the full compact published closure, not just import names.
    for name, row in records.items():
        path = (BASE/name).resolve()
        require(path.is_relative_to(BASE), "input escapes publication directory")
        require(digest(path) == row["publication_sha256"], "changed input: "+name)
        if not name.startswith("browser/"):
            require(row["historical_sha256"] == row["publication_sha256"],
                    "code/data adaptation is not permitted by this runner: "+name)
    checker = BASE/case["checker"]
    historical_path = BASE/case["historical_report"]
    historical = json.loads(historical_path.read_text())
    require(historical["status"] == case["historical_status"], "wrong historical status")
    require(historical["input_sha256"] == case["original_pins"], "historical pins differ")
    sys.path[:0] = [str(BASE/"verification"), str(BASE/"breaker"), str(BASE/"maker")]
    spec = importlib.util.spec_from_file_location(args.case, checker)
    require(spec is not None and spec.loader is not None, "missing checker module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[args.case] = module
    spec.loader.exec_module(module)
    require(module.PINS == case["original_pins"], "checker pins differ from historical manifest")
    changed = dict(module.PINS)
    substitutions = []
    for name, new_hash in case["sanitized_text_pins"].items():
        require(name.startswith("browser/") and name in changed, "non-text substitution")
        row = records[name]
        require(row["historical_sha256"] == changed[name], "wrong historical text binding")
        require(row["publication_sha256"] == new_hash, "wrong sanitized text binding")
        substitutions.append(dict(path=name, old_sha256=changed[name], new_sha256=new_hash,
                                  transformation=row["transformation"]))
        changed[name] = new_hash
    # This is the entire publication adaptation. All mathematical functions,
    # states, witnesses, target generators, policies and controls are unchanged.
    module.PINS = changed
    output.parent.mkdir(parents=True, exist_ok=True)
    sys.argv = [str(checker), *[str(output) if x == "{output}" else x for x in case["argv"]]]
    code = module.main()
    require(type(code) is int, "checker did not return an exit code")
    replay = json.loads(output.read_text())
    receipt = dict(schema="snaky-publication-finite-replay-v1", status="rejected",
                   case=args.case, checker=case["checker"], checker_sha256=digest(checker),
                   runner_sha256=digest(__file__), manifest_sha256=digest(MANIFEST),
                   historical_report=case["historical_report"],
                   historical_report_sha256=digest(historical_path),
                   replay_report_sha256=digest(output), checker_exit_code=code,
                   text_pin_substitutions=substitutions,
                   created_utc=datetime.now(timezone.utc).isoformat())
    require(replay["input_sha256"] == changed, "replay omitted or changed explicit input pins")
    old_math, new_math = dict(historical), dict(replay)
    old_math.pop("input_sha256"); new_math.pop("input_sha256")
    execution = {}
    for key in case["allowed_execution_fields"]:
        require(key in {"created_utc", "utc", "process_cpu_seconds", "cpu_seconds", "elapsed_seconds"},
                "unnamed provenance exception")
        old, new = old_math.pop(key), new_math.pop(key)
        if key in {"created_utc", "utc"}:
            datetime.fromisoformat(new.replace("Z", "+00:00"))
        else:
            require(type(new) in (int, float) and math.isfinite(new) and new >= 0,
                    "invalid execution metric")
        execution[key] = dict(historical=old, replay=new)
    receipt["execution_field_differences"] = execution
    difference = first_difference(old_math, new_math)
    receipt["mathematical_difference"] = difference
    if code == 0 and difference is None:
        receipt["status"] = "publication_replay_mathematically_identical"
    with receipt_path.open("x") as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True); stream.write("\n")
    print(json.dumps(dict(case=args.case, status=receipt["status"], receipt=str(receipt_path))))
    return int(receipt["status"] != "publication_replay_mathematically_identical")


if __name__ == "__main__":
    raise SystemExit(main())
