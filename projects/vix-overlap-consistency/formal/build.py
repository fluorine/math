#!/usr/bin/env python3
"""Compile the project's Lean modules serially against pinned dependencies."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
LEAN_VERSION = "4.34.1"
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
MATHLIB_COMMIT = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^(?:public )?import\s+([^\n]+)", re.MULTILINE)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide)\b")


def run(args: list[str], env: dict[str, str], *, capture: bool = False) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.STDOUT if capture else None)
    if result.returncode:
        if capture and result.stdout:
            print(result.stdout, end="")
        raise SystemExit(result.returncode)
    return result.stdout or ""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("VIX_LEAN", "lean"))
    parser.add_argument("--target", default="VixOverlap.Audit")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if lean is None:
        raise SystemExit("Pinned Lean 4.34.1 is required; set VIX_LEAN or use --lean.")
    lean = str(Path(lean).resolve())
    lake = str(Path(lean).with_name("lake"))
    env = dict(os.environ)
    env["PATH"] = str(Path(lean).parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        env[key] = "1"
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env["MATHLIB_CACHE_DIR"] = str(ROOT / ".lake" / "mathlib-cache")
    version = run([lean, "--version"], env, capture=True).strip()
    if f"version {LEAN_VERSION}," not in version or LEAN_COMMIT not in version:
        raise SystemExit(f"Wrong Lean toolchain: {version}")
    print(version, flush=True)

    manifest_path = ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB_COMMIT:
        raise SystemExit("Mathlib manifest does not match the pinned revision.")
    packages = ROOT / manifest["packagesDir"]
    if any(not (packages / p["name"] / ".git").exists() for p in manifest["packages"]):
        # The checked-in manifest supplies all dependency commits. `update` is
        # deliberately avoided: it may advance inherited branch revisions.
        run([lake, "env", "true"], env)
    for package in manifest["packages"]:
        folder = packages / package["name"]
        actual = run(["git", "-C", str(folder), "rev-parse", "HEAD"], env, capture=True).strip()
        if actual != package["rev"]:
            raise SystemExit(f"Dependency {package['name']} is at {actual}, expected {package['rev']}.")
        dirty = run(["git", "-C", str(folder), "diff", "--name-only", "HEAD"], env, capture=True)
        if dirty.strip():
            raise SystemExit(f"Modified dependency sources in {package['name']}:\n{dirty}")

    ordered: list[tuple[str, Path]] = []
    external: set[str] = set()
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise SystemExit(f"Import cycle at {module}.")
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            external.add(module)
            return
        visiting.add(module)
        text = source.read_text()
        if FORBIDDEN.search(text):
            raise SystemExit(f"Forbidden proof placeholder, axiom, or native oracle in {source}.")
        for clause in IMPORT.findall(text):
            for dependency in clause.split("--", 1)[0].split():
                visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append((module, source))

    visit(args.target)
    if not ordered:
        raise SystemExit(f"No local source for target {args.target}.")

    # Only fetch the Mathlib import closure when a direct imported object is
    # absent. The cache's verified source hashes select the upstream artifacts.
    mathlib_build = packages / "mathlib" / ".lake" / "build" / "lib" / "lean"
    missing = [m for m in external if m.startswith("Mathlib.") and
               not (mathlib_build / (m.replace(".", "/") + ".olean")).is_file()]
    if missing:
        run([lake, "exe", "cache", "get", *sorted(external)], env)

    env["LEAN_PATH"] = run([lake, "env", "printenv", "LEAN_PATH"], env, capture=True).strip()
    build = ROOT / ".lake" / "build" / "lib" / "lean"
    # Every local module is always recompiled. Dependencies are immutable and
    # reused. This cannot erase another module's source or another task's files.
    outputs: list[str] = []
    for module, source in ordered:
        output = build / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"Checking {module}", flush=True)
        result = run(["nice", "-n", "19", lean, "-j1", "-M4096", "-o", str(output), str(source)], env, capture=True)
        print(result, end="", flush=True)
        outputs.append(result)
    combined = "".join(outputs)
    reported = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", combined)
    for group in reported:
        unexpected = {a.strip() for a in group.split(",") if a.strip()} - ALLOWED_AXIOMS
        if unexpected:
            raise SystemExit(f"Unexpected theorem axioms: {sorted(unexpected)}")
    if args.target.endswith("Audit") and not reported:
        raise SystemExit("Audit did not print any theorem axiom dependencies.")
    print(f"PASS: {len(ordered)} local modules freshly compiled; exit status 0.", flush=True)


if __name__ == "__main__":
    main()
