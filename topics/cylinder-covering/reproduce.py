#!/usr/bin/env python3
"""Reproduce the exact certificates and, optionally, the complete Lean audit."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


TOPIC = Path(__file__).resolve().parent
REVISION = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"


def check_sources():
    sources = TOPIC / "sources"
    manifest = json.loads((sources / "manifest.json").read_text(encoding="utf-8"))
    if manifest["revision"] != REVISION:
        raise SystemExit("Unexpected source revision")
    blob_count = 0
    for entry in manifest["files"]:
        path = sources / entry["path"]
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise SystemExit("Source SHA-256 mismatch: " + entry["path"])
        if entry.get("git_blob"):
            git_object = b"blob " + str(len(data)).encode("ascii") + b"\0" + data
            if hashlib.sha1(git_object).hexdigest() != entry["git_blob"]:
                raise SystemExit("Source Git blob mismatch: " + entry["path"])
            blob_count += 1
    print("PASS: {} source SHA-256 hashes and {} Git blob hashes.".format(
        len(manifest["files"]), blob_count), flush=True)


def reproduce(script, record):
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(
        [sys.executable, str(TOPIC / "verification" / script)],
        cwd=TOPIC.parents[1], env=environment,
        capture_output=True, text=True, timeout=120, check=False,
    )
    print(result.stdout, end="", flush=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    if result.returncode:
        raise SystemExit("Certificate failed: " + script)
    expected = (TOPIC / "verification" / record).read_text(encoding="utf-8")
    if result.stdout != expected:
        raise SystemExit("Certificate output differs from recorded output: " + record)
    print("PASS: {} matches {}.".format(script, record), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--formal", action="store_true", help="also run the Lean build, kernel replay and negative controls")
    parser.add_argument("--lean", help="path to the pinned Lean 4.34.1 executable")
    parser.add_argument("--fresh", action="store_true", help="recompile every local proof module")
    args = parser.parse_args()
    os.nice(19)
    formal = TOPIC / "formal"
    build = formal / ".cache" / "build"
    build.mkdir(parents=True, exist_ok=True)
    # Share the formal compiler's lock: only one local computational job runs.
    with (build / "compile.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        check_sources()
        subprocess.run([sys.executable, str(formal / "tools" / "generate_certificates.py"), "--check"], check=True)
        reproduce("verify.py", "last-run.txt")
        reproduce("secant_verify.py", "secant-last-run.txt")
    print("REPRODUCED: exact independent certificates, generated proof data and source pins.", flush=True)
    if args.formal:
        command = [sys.executable, str(formal / "build.py"), "--target", "TetrahedronCover.Audit",
                   "--replay", "--negative-controls"]
        if args.lean:
            command += ["--lean", args.lean]
        if args.fresh:
            command.append("--fresh")
        subprocess.run(command, cwd=formal, check=True)
        print("REPRODUCED: Lean theorem checks, axiom audit, local kernel replay and negative controls.", flush=True)
    else:
        print("Lean was not run by this invocation. Use --formal for the separate kernel audit.")


if __name__ == "__main__":
    main()
