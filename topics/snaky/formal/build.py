#!/usr/bin/env python3
"""Generate certificate proof modules and compile them serially with Lean 4.34.1."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import shutil
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
BUILD = HERE / ".build"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--target", default="Snaky.Result19")
    parser.add_argument("--no-generate", action="store_true")
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--module-seconds", type=int, default=180)
    args = parser.parse_args()
    if not args.lean:
        parser.error("Lean 4.34.1 is required; pass --lean /absolute/path/to/lean")
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.34.1," not in version:
        raise SystemExit(f"Unexpected compiler: {version}")
    if not args.no_generate:
        subprocess.run([sys.executable, str(HERE / "tools" / "cards2lean.py"),
                        str(HERE.parent / "certificate" / "snaky19.cards.txt"), str(HERE),
                        "--name=Gen19", "--units=400000", "--max-cards=30", "--max-cells=5"],
                       check=True)
    BUILD.mkdir(exist_ok=True)
    state_path = BUILD / "state.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {}
    environment = os.environ.copy()
    environment["LEAN_PATH"] = str(BUILD / "lib")
    environment["OMP_NUM_THREADS"] = "1"
    started = time.monotonic()
    records, visited, active = [], {}, set()

    def compile_module(module):
        if module in visited:
            return visited[module]
        if module in active:
            raise RuntimeError(f"Import cycle at {module}")
        active.add(module)
        source = HERE / (module.replace(".", "/") + ".lean")
        raw = source.read_bytes()
        dependencies = []
        for line in raw.decode().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    if dependency.startswith("Snaky."):
                        dependencies.append(compile_module(dependency))
        digest = hashlib.sha256(raw + version.encode() + "".join(dependencies).encode()).hexdigest()
        output = BUILD / "lib" / (module.replace(".", "/") + ".olean")
        if state.get(module, {}).get("digest") == digest and output.exists():
            active.remove(module)
            visited[module] = digest
            return digest
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, "-j", "1", "-M", str(args.memory_mb), "-R", str(HERE),
                   "-o", str(output), str(source)]
        print(f"CHECK {module}", flush=True)
        before = time.monotonic()
        result = subprocess.run(command, cwd=HERE, env=environment, capture_output=True,
                                text=True, timeout=args.module_seconds)
        seconds = round(time.monotonic() - before, 4)
        log = result.stdout + result.stderr
        (BUILD / (module + ".log")).write_text(log)
        if log:
            print(log, end="", flush=True)
        if result.returncode:
            raise SystemExit(f"Lean rejected {module} (exit {result.returncode}); see {BUILD}")
        if "declaration uses 'sorry'" in log:
            raise SystemExit(f"Proof placeholder in {module}")
        record = dict(module=module, digest=digest, seconds=seconds, command=command)
        state[module] = record
        state_path.write_text(json.dumps(state, indent=2) + "\n")
        records.append(record)
        active.remove(module)
        visited[module] = digest
        return digest

    compile_module(args.target)
    report = dict(status="compiled", target=args.target, lean=version,
                  threads=1, memory_limit_mb=args.memory_mb,
                  timeout_per_module_seconds=args.module_seconds,
                  host=platform.platform(), modules_in_dependency_closure=len(visited),
                  modules_compiled_this_run=len(records),
                  elapsed_seconds=round(time.monotonic() - started, 4),
                  child_max_rss=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  child_max_rss_unit="bytes" if sys.platform == "darwin" else "KiB",
                  certificate_sha256=hashlib.sha256(
                      (HERE.parent / "certificate" / "snaky19.cards.txt").read_bytes()).hexdigest(),
                  records=records)
    (BUILD / "last-build.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "records"}), flush=True)


if __name__ == "__main__":
    main()
