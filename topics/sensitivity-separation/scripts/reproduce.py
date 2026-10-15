#!/usr/bin/env python3
"""One serial, bounded reproduction command; stdlib Python 3.9+ only."""
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]


def run(relative, *args, timeout=30):
    env=dict(os.environ,OMP_NUM_THREADS="1",OPENBLAS_NUM_THREADS="1",MKL_NUM_THREADS="1")
    subprocess.run([sys.executable,str(ROOT/relative),*args],cwd=ROOT,
                   env=env,timeout=timeout,check=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-sources",action="store_true",
                        help="also recover and hash-check the pinned source cache")
    args=parser.parse_args()
    if args.fetch_sources:
        run("scripts/fetch_sources.py",timeout=180)
    run("checks/label_contract.py","--self-test")
    run("checks/profile_local.py")
    run("checks/seed_certificate.py","--check",str(ROOT/"checks/seed-certificate.json"))
    run("checks/independent_audit.py",timeout=120)
    print("All finite checks and exact seed certificates passed. Infinite claims rely on the independently audited written proofs; no Lean build was run.")


if __name__=="__main__":
    main()
