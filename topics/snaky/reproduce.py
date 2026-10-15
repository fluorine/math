#!/usr/bin/env python3
"""Independently verify the 19-move certificate; optionally reconstruct it."""

import argparse
from pathlib import Path
import hashlib
import os
import subprocess
import sys
import tempfile


TOPIC = Path(__file__).resolve().parent
EXPECTED = {
    "sieben-20-cards.txt": "c15deef097541e2413cc543916e8d5773ffa398f5be66ca976c73f894c7fd832",
    "gotrevor-15x15-cards.txt": "94fc96c8e9a7bbd99748f8668fd8ba22519fe9ea771ec76fe1c3ab94ee283084",
}
FINAL_SHA256 = "baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e"


def run(*arguments, expected=0):
    completed = subprocess.run([sys.executable, *map(str, arguments)],
                               cwd=TOPIC.parents[1], timeout=120, check=False)
    if completed.returncode != expected:
        raise SystemExit(f"Unexpected exit {completed.returncode}, expected {expected}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reconstruct", action="store_true",
                        help="rerun the bounded construction and require identical final bytes")
    parser.add_argument("--baselines", action="store_true",
                        help="also reproduce both public baseline audits and a 20-move transcript")
    args = parser.parse_args()
    # All subprocesses are serial, stdlib-only and deterministic.
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    for name, expected in EXPECTED.items():
        actual = hashlib.sha256((TOPIC / "reference" / name).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Reference SHA-256 mismatch: {name}")
    run("-m", "unittest", "discover", "-s", TOPIC / "verification", "-p", "test_*.py")
    checker = TOPIC / "verification" / "verify_cards.py"
    baseline = TOPIC / "reference" / "sieben-20-cards.txt"
    certificate = TOPIC / "certificate" / "snaky19.cards.txt"
    if hashlib.sha256(certificate.read_bytes()).hexdigest() != FINAL_SHA256:
        raise SystemExit("Final certificate SHA-256 mismatch")
    run(checker, certificate, "--max-root-height", "19")
    run(TOPIC / "verification" / "check_candidate_controls.py", certificate)
    with tempfile.TemporaryDirectory(prefix="snaky-reproduction-") as temporary:
        temporary = Path(temporary)
        if args.reconstruct:
            report = temporary / "construction.json"
            run(TOPIC / "constructor" / "history_closure.py", baseline,
                "--extra-catalog", TOPIC / "reference" / "gotrevor-15x15-cards.txt",
                "--budget", "19", "--seconds", "100", "--nodes", "2000000",
                "--output", report)
            compact = temporary / "compact.cards.txt"
            run(TOPIC / "constructor" / "prune_certificate.py", report.with_suffix(".cards.txt"),
                "--output", compact, "--map", temporary / "map.json")
            if compact.read_bytes() != certificate.read_bytes():
                raise SystemExit("Reconstruction differs from the delivered certificate")
            print("Reconstruction is byte-for-byte identical.", flush=True)
        if args.baselines:
            for name in EXPECTED:
                run(checker, TOPIC / "reference" / name)
            run(checker, baseline, "--max-root-height", "19", expected=1)
            routes = temporary / "baseline_routes.json"
            run(TOPIC / "constructor" / "analyze_routes.py", baseline, "--output", routes)
            transcript_checker = TOPIC / "verification" / "verify_transcript.py"
            run(transcript_checker, baseline, routes, "--plane")
            # This witness intentionally includes an off-board Breaker response.
            run(transcript_checker, baseline, routes, expected=1)
    print("VERIFIED: Snaky within 19 Maker moves; see SOUNDNESS.md for the infinite-board proof.")


if __name__ == "__main__":
    main()
