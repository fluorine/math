#!/usr/bin/env python3
"""Independently check the separate 15x15, 24-move certificate.

The optional reconstruction compares both certificate and provenance-map bytes.
Lean kernel checking is a separate formal/build.py workflow documented in
RESULT-15X15-24.md; this command does not run Lean or assert kernel verification.
"""

import argparse
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import sys


TOPIC = Path(__file__).resolve().parent
FINAL_SHA256 = "ff88668bddcbc4bb4a0dfa9794ac411b1492ddbcb22013621f1723f9cc3ef567"
STEP_TIMEOUT_SECONDS = 150


def run(environment, *arguments):
    """Run one serial step, also stopping its own children on interruption."""
    command = [sys.executable, *map(str, arguments)]
    process = subprocess.Popen(command, cwd=TOPIC.parents[1], env=environment,
                               start_new_session=True)
    try:
        returncode = process.wait(timeout=STEP_TIMEOUT_SECONDS)
    except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
        # Reconstruction starts its own constructor subprocess. Keep a timed
        # out step from leaving that computation running behind this script.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        reason = "timed out" if isinstance(error, subprocess.TimeoutExpired) else "was interrupted"
        raise SystemExit(f"Reproduction step {reason}: {arguments[0]}") from None
    if returncode != 0:
        raise SystemExit(f"Reproduction stopped: {arguments[0]} exited with {returncode}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reconstruct", action="store_true",
                        help="regenerate from pinned inputs and require identical certificate and map bytes")
    args = parser.parse_args()
    certificate = TOPIC / "certificate" / "snaky15x15-24.cards.txt"
    try:
        digest = hashlib.sha256(certificate.read_bytes()).hexdigest()
    except OSError as error:
        raise SystemExit(f"Cannot read the 15x15 certificate: {error}") from None
    if digest != FINAL_SHA256:
        raise SystemExit("15x15, 24-move certificate SHA-256 mismatch")

    environment = os.environ.copy()
    environment.update(PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0")
    for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                 "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS"):
        environment[name] = "1"
    run(environment, "-m", "unittest", "discover", "-s", TOPIC / "verification", "-p", "test_*.py")
    run(environment, TOPIC / "verification" / "verify_cards.py", certificate,
        "--max-root-height", "24")
    run(environment, TOPIC / "verification" / "check_candidate_controls.py", certificate)
    if args.reconstruct:
        run(environment, TOPIC / "constructor" / "package_15x15.py", "--reconstruct", "--check")
        print("Reconstruction matched the delivered certificate and provenance map byte for byte.", flush=True)
    print("COMPUTATIONAL CHECKS PASSED: Snaky on 15x15 within 24 Maker claims. "
          "This command did not perform Lean kernel verification.", flush=True)


if __name__ == "__main__":
    main()
