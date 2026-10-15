#!/usr/bin/env python3
"""Package the separate 15x15, 24-move candidate with exact source provenance.

Use --reconstruct --check to regenerate it from the pinned catalogs and require
byte-for-byte equality with the delivered certificate and map. Without
--reconstruct, read the saved experiment (or --candidate). This program is a
construction aid, not the independent mathematical verifier or Lean checker.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from analyze_routes import Hint, ORIENTS, parse
from history_closure import append_catalog, serialize
from prune_certificate import prune


TOPIC = Path(__file__).resolve().parents[1]
SOURCES = (
    ("gotrevor_15x15", "reference/gotrevor-15x15-cards.txt", 8671,
     "94fc96c8e9a7bbd99748f8668fd8ba22519fe9ea771ec76fe1c3ab94ee283084"),
    ("sieben_20", "reference/sieben-20-cards.txt", 1738,
     "c15deef097541e2413cc543916e8d5773ffa398f5be66ca976c73f894c7fd832"),
    ("snaky_19", "certificate/snaky19.cards.txt", 3468,
     "baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e"),
)
CANDIDATE_SHA256 = "3c997a486a943d43a5858c2d4bfd3af67c88223aeb09f207be8f88b06ec6e411"
FINAL_SHA256 = "ff88668bddcbc4bb4a0dfa9794ac411b1492ddbcb22013621f1723f9cc3ef567"
DEFAULT_OUTPUT = TOPIC / "certificate" / "snaky15x15-24.cards.txt"
DEFAULT_MAP = TOPIC / "certificate" / "snaky15x15-24.map.json"


def source_catalogs():
    combined, sources = [], []
    for name, relative, count, expected in SOURCES:
        cards, meta = parse(TOPIC / relative)
        if meta["source_sha256"] != expected or len(cards) != count:
            raise ValueError(f"Pinned source differs: {relative}")
        sources.append(dict(source=name, path=relative, offset=len(combined),
                            card_count=count, sha256=expected))
        append_catalog(combined, cards)
    return combined, sources


def package(candidate, combined, sources):
    cards, meta = parse(candidate)
    if meta["source_sha256"] != CANDIDATE_SHA256:
        raise ValueError("Unpruned candidate SHA-256 differs from the checked experiment")
    if (meta["rows"], meta["columns"]) != (15, 15):
        raise ValueError("The candidate must describe a 15x15 board")
    if cards[:len(combined)] != combined:
        raise ValueError("Candidate catalog prefix does not match the claimed source order")
    g = tuple(meta["root_transform"])
    root = Hint(meta["root"], ORIENTS.index(g[:4]), g[4], g[5])
    compact, root, order = prune(cards, root)
    if compact[root.child].height != 24 or compact[root.child].required:
        raise ValueError("Expected an empty-root certificate with height 24")
    raw = serialize(compact, meta, root).encode("ascii")
    digest = hashlib.sha256(raw).hexdigest()
    if digest != FINAL_SHA256:
        raise ValueError("Compact certificate SHA-256 differs from the recorded candidate")

    def origin(index):
        for source in sources:
            if source["offset"] <= index < source["offset"] + source["card_count"]:
                return source["source"], index - source["offset"]
        return "constructed_24", index - len(combined)

    provenance = [dict(compact_id=j, combined_id=i, source=origin(i)[0],
                       source_id=origin(i)[1]) for j, i in enumerate(order)]
    counts = Counter(row["source"] for row in provenance)
    report = dict(
        schema="snaky15x15-24-package-v1",
        purpose="Deterministic packaging and provenance; not independent verification",
        input_sha256=meta["source_sha256"], output_sha256=digest,
        input_cards=len(cards), output_cards=len(compact), output_bytes=len(raw),
        original_root=meta["root"], compact_root=root.json(),
        rows=15, columns=15, root_height=24,
        construction=dict(algorithm="constructor/history_closure.py", maker_budget=24,
                          node_limit=2000000, wall_limit_seconds=120,
                          threads=1, randomized=False),
        source_catalogs=sources,
        source_counts={name: counts[name] for name in
                       [source["source"] for source in sources] + ["constructed_24"]},
        cards=provenance)
    return raw, (json.dumps(report, indent=2) + "\n").encode("ascii"), report


def reconstruct(directory):
    report = directory / "construction.json"
    command = [sys.executable, str(TOPIC / "constructor" / "history_closure.py"),
               str(TOPIC / SOURCES[0][1])]
    for _, relative, _, _ in SOURCES[1:]:
        command.extend(("--extra-catalog", str(TOPIC / relative)))
    command.extend(("--budget", "24", "--seconds", "120", "--nodes", "2000000",
                    "--output", str(report)))
    environment = os.environ.copy()
    environment.update(PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0", OMP_NUM_THREADS="1")
    subprocess.run(command, cwd=TOPIC.parents[1], env=environment,
                   timeout=150, check=True)
    if json.loads(report.read_text())["status"] != "constructed":
        raise ValueError("The bounded construction did not produce a complete candidate")
    return report.with_suffix(".cards.txt")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, help="read an existing unpruned candidate")
    parser.add_argument("--reconstruct", action="store_true",
                        help="rerun the deterministic bounded construction from pinned inputs")
    parser.add_argument("--check", action="store_true",
                        help="compare certificate and provenance bytes without writing them")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--map", type=Path, default=DEFAULT_MAP)
    args = parser.parse_args()
    if args.candidate is not None and args.reconstruct:
        parser.error("--candidate and --reconstruct are mutually exclusive")
    combined, sources = source_catalogs()
    with tempfile.TemporaryDirectory(prefix="snaky15x15-24-") as temporary:
        candidate = (reconstruct(Path(temporary)) if args.reconstruct else
                     args.candidate or TOPIC / "experiments" / "next-step" / "15-board-24.cards.txt")
        raw, mapping, report = package(candidate, combined, sources)
        for path, content in ((args.output, raw), (args.map, mapping)):
            if args.check:
                if not path.exists() or path.read_bytes() != content:
                    raise ValueError(f"Packaged bytes differ or are missing: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
    summary = {key: report[key] for key in (
        "output_sha256", "output_cards", "output_bytes", "compact_root", "root_height", "source_counts")}
    summary["status"] = "identical" if args.check else "packaged"
    summary["independent_verification_performed"] = False
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
