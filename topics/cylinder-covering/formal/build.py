#!/usr/bin/env python3
"""Compile the pinned tetrahedron proof serially, with dependency-aware caching."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
BUILD = HERE / '.cache' / 'build'
MATHLIB_REV = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
UPSTREAM_REV = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--target', default='TetrahedronCover.Audit')
    parser.add_argument('--memory-mb', type=int, default=3072)
    parser.add_argument('--resident-mb', type=int, default=2300)
    parser.add_argument('--module-seconds', type=int, default=240)
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--replay', action='store_true',
                        help='Recheck each local module with the standalone Lean kernel replay tool')
    parser.add_argument('--negative-controls', action='store_true',
                        help='Require rejection of a false benchmark bound and a damaged polynomial identity')
    args = parser.parse_args()
    os.nice(19)
    def interrupted(signum, frame):
        raise InterruptedError("Build interrupted; stopping only its owned compiler")
    signal.signal(signal.SIGTERM, interrupted)
    if not args.lean:
        parser.error('Lean 4.34.1 is required; pass --lean /absolute/path/to/lean')
    if not re.fullmatch(r'(?:OAI|TetrahedronCover)(?:\.[A-Za-z0-9_]+)*', args.target):
        parser.error('The target must be a module in this project')
    # Preserve the executable name while invoking an elan proxy, and ask it
    # within this project so lean-toolchain selects the intended release.
    requested_lean = str(Path(args.lean).expanduser().absolute())
    prefix = subprocess.check_output([requested_lean, '--print-prefix'], cwd=HERE, text=True).strip()
    lean = str((Path(prefix) / 'bin' / 'lean').resolve())
    lake = str(Path(lean).with_name('lake'))
    version = subprocess.check_output([lean, '--version'], cwd=HERE, text=True).strip()
    if ('version 4.34.1,' not in version
            or 'commit 5045d0056413266e57c625dcd7c365b10e377c52,' not in version):
        raise SystemExit('Unexpected compiler: ' + version)
    mathlib = HERE / '.lake' / 'packages' / 'mathlib'
    if not mathlib.is_dir():
        raise SystemExit('Install the pinned dependencies first; see formal/README.md')
    revision = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != MATHLIB_REV:
        raise SystemExit('Unexpected mathlib revision: ' + revision)
    dependencies = json.loads((HERE / 'lake-manifest.json').read_text())
    for package in dependencies['packages']:
        directory = HERE / '.lake' / 'packages' / package['name']
        actual = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise SystemExit('Unexpected dependency revision: ' + package['name'])
        dirty = subprocess.check_output(
            ['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
        if dirty:
            raise SystemExit('Tracked dependency sources are modified: ' + package['name'])
    manifest = json.loads((HERE / 'upstream-manifest.json').read_text())
    if manifest['revision'] != UPSTREAM_REV or manifest['repository'] != 'https://github.com/openai/math':
        raise SystemExit('Unexpected OpenAI source pin')
    for entry in manifest['files']:
        original = (HERE / entry['original_path']).read_bytes()
        if hashlib.sha256(original).hexdigest() != entry['sha256']:
            raise SystemExit('Pinned source changed: ' + entry['original_path'])
        git_object = b'blob ' + str(len(original)).encode() + b'\0' + original
        if hashlib.sha1(git_object).hexdigest() != entry['git_blob']:
            raise SystemExit('Pinned Git blob mismatch: ' + entry['original_path'])
        expected = original
        if entry.get('import_replacement'):
            prefix = b'import Mathlib\n'
            if not original.startswith(prefix):
                raise SystemExit('Unexpected upstream import: ' + entry['path'])
            expected = entry['import_replacement'].encode() + original[len(prefix):]
        if entry.get('module_interface'):
            lines = expected.decode().splitlines(keepends=True)
            end = 0
            for i, line in enumerate(lines):
                if line.startswith('import '):
                    lines[i] = 'public ' + line
                    end = i + 1
            lines.insert(end, '\n@[expose] public section\n')
            expected = ('module\n' + ''.join(lines)).encode()
        if (HERE / entry['path']).read_bytes() != expected:
            raise SystemExit('Upstream proof body changed: ' + entry['path'])
    replay_manifest = json.loads((HERE / 'tools' / 'replay-manifest.json').read_text())
    replay_original = (HERE / replay_manifest['original_path']).read_bytes()
    if hashlib.sha256(replay_original).hexdigest() != replay_manifest['sha256']:
        raise SystemExit('Upstream kernel replay driver changed')
    replay_source = replay_original.decode().replace(replay_manifest['replace_from'], replay_manifest['replace_to'])
    if (HERE / replay_manifest['adapted_path']).read_text() != replay_source:
        raise SystemExit('Kernel replay adaptation differs from the documented change')
    BUILD.mkdir(parents=True, exist_ok=True)
    lock = (BUILD / 'compile.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    started = time.monotonic()
    environment = dict(os.environ, OMP_NUM_THREADS='1', LEAN_NUM_THREADS='1')
    environment['PATH'] = str(Path(lean).parent) + os.pathsep + environment.get('PATH', '')
    package_path = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=HERE, env=environment, text=True).strip()
    environment['LEAN_PATH'] = str(BUILD / 'lib') + os.pathsep + package_path
    state_path = BUILD / 'state.json'
    state = json.loads(state_path.read_text()) if state_path.exists() and not args.fresh else {}
    dependency_pin = hashlib.sha256((HERE / 'lake-manifest.json').read_bytes()).hexdigest()
    records, visited, active = [], {}, set()

    def run_checked(command, label, expect_rejection=False):
        before = time.monotonic()
        with tempfile.TemporaryFile(mode='w+') as capture:
            process = subprocess.Popen(command, cwd=HERE, env=environment,
                                       stdout=capture, stderr=subprocess.STDOUT)
            peak_rss_kib, failure = 0, None
            try:
                while process.poll() is None:
                    if time.monotonic() - before > args.module_seconds:
                        raise RuntimeError('Module time budget exceeded: ' + label)
                    rss = subprocess.run(['ps', '-o', 'rss=', '-p', str(process.pid)],
                                         capture_output=True, text=True)
                    if rss.stdout.strip():
                        peak_rss_kib = max(peak_rss_kib, int(rss.stdout.strip()))
                        if peak_rss_kib > args.resident_mb * 1024:
                            raise RuntimeError(f'Module resident memory exceeded {args.resident_mb} MiB '
                                               f'({peak_rss_kib/1024:.1f} MiB observed): ' + label)
                    time.sleep(0.1)
            except BaseException as error:
                failure = error
                if process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
            capture.seek(0)
            log = capture.read()
        (BUILD / (label + '.log')).write_text(log)
        if log:
            print(log, end='', flush=True)
        if failure:
            raise failure
        if expect_rejection:
            if process.returncode == 0 or 'unsolved goals' not in log:
                raise SystemExit('Negative control did not fail at its proof obligation: ' + label)
            return dict(control=label, status='rejected',
                        seconds=round(time.monotonic()-before, 4), peak_rss_kib=peak_rss_kib,
                        diagnostic=log)
        if process.returncode:
            raise SystemExit(f'Lean rejected {label} (exit {process.returncode})')
        if "declaration uses 'sorry'" in log:
            raise SystemExit('Proof placeholder in ' + label)
        return dict(module=label, seconds=round(time.monotonic()-before, 4), peak_rss_kib=peak_rss_kib)

    def output_hashes(output):
        paths = [output, Path(str(output)+'.server'), Path(str(output)+'.private')]
        return {str(p.relative_to(BUILD)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in paths if p.exists()}

    def compile_module(module):
        if module in visited:
            return visited[module]
        if module in active:
            raise RuntimeError('Import cycle: ' + module)
        active.add(module)
        source = HERE / (module.replace('.', '/') + '.lean')
        raw = source.read_bytes()
        forbidden = re.search(
            r'(?m)^\s*(?:(?:private|public|noncomputable)\s+)*(?:unsafe|partial|axiom)\b'
            r'|\b(?:native_decide|sorryAx|admit)\b', raw.decode())
        if forbidden:
            raise SystemExit('Unsupported proof shortcut in ' + module + ': ' + forbidden.group().strip())
        dependencies = []
        for line in raw.decode().splitlines():
            if line.startswith(('import ', 'public import ')):
                parts = line.split('--')[0].split()
                for dep in parts[2:] if parts[0] == 'public' else parts[1:]:
                    if dep == 'TetrahedronCover' or dep.startswith(('OAI.', 'TetrahedronCover.')):
                        dependencies.append(compile_module(dep))
        digest = hashlib.sha256(raw + version.encode() + dependency_pin.encode() + ''.join(dependencies).encode()).hexdigest()
        output = BUILD / 'lib' / (module.replace('.', '/') + '.olean')
        cached = state.get(module, {})
        if (cached.get('digest') == digest and output.exists()
                and cached.get('outputs') == output_hashes(output)):
            active.remove(module)
            visited[module] = digest
            return digest
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, '-j', '1', '-M', str(args.memory_mb), '-DmaxHeartbeats=4000000',
                   '-DmaxRecDepth=10000', '-R', str(HERE), '-o', str(output), str(source)]
        print('CHECK ' + module, flush=True)
        record = dict(run_checked(command, module), digest=digest,
                      source_sha256=hashlib.sha256(raw).hexdigest(), outputs=output_hashes(output))
        if source.read_bytes() != raw:
            raise SystemExit('Source changed during compilation; rerun the build: ' + module)
        state[module] = record
        state_path.write_text(json.dumps(state, indent=2)+'\n')
        records.append(record)
        active.remove(module)
        visited[module] = digest
        return digest

    compile_module(args.target)
    axiom_audit = {}
    if 'TetrahedronCover.Audit' in visited:
        audit_source = (HERE / 'TetrahedronCover' / 'Audit.lean').read_text()
        expected_names = re.findall(r'^#print axioms ([\w.]+)$', audit_source, re.M)
        if not expected_names:
            raise SystemExit('The audit contains no theorem axiom checks')
        audit_log = (BUILD / 'TetrahedronCover.Audit.log').read_text()
        for name, raw_axioms in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", audit_log):
            axiom_audit[name] = [a.strip() for a in raw_axioms.split(',') if a.strip()]
        for name in re.findall(r"'([\w.]+)' does not depend on any axioms", audit_log):
            axiom_audit[name] = []
        if set(axiom_audit) != set(expected_names):
            raise SystemExit('Missing or unexpected theorem in the axiom audit')
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for name, axioms in axiom_audit.items():
            if not set(axioms) <= allowed:
                raise SystemExit('Unexpected foundational axiom in ' + name + ': ' + str(axioms))
    replay_records = []
    if args.replay:
        checker = str(HERE / replay_manifest['adapted_path'])
        # Bind replay evidence to the actual artifacts, including local imports.
        # Conservatively replay the closure if any compiled part changes.
        replay_artifacts = hashlib.sha256(json.dumps(
            {module: state[module]['outputs'] for module in visited},
            sort_keys=True).encode()).hexdigest()
        replay_state_path = BUILD / 'replay-state.json'
        replay_state = (json.loads(replay_state_path.read_text())
                        if replay_state_path.exists() and not args.fresh else {})
        for module in visited:
            replay_digest = hashlib.sha256(
                (visited[module] + replay_source + replay_artifacts).encode()).hexdigest()
            cached_replay = replay_state.get(module, {})
            if cached_replay.get('digest') == replay_digest:
                replay_records.append(cached_replay)
                continue
            print('REPLAY ' + module, flush=True)
            replay_record = run_checked(
                [lean, '-j', '1', '-M', str(args.memory_mb), '--run', checker, '--verbose', module],
                module+'.replay')
            replay_record['digest'] = replay_digest
            replay_record['artifact_closure_sha256'] = replay_artifacts
            replay_records.append(replay_record)
            replay_state[module] = replay_record
            replay_state_path.write_text(json.dumps(replay_state, indent=2)+'\n')
    controls = []
    if args.negative_controls:
        if 'TetrahedronCover.BenchmarkPolynomials' not in visited:
            raise SystemExit('Negative controls require a target importing BenchmarkPolynomials')
        cases = {
            'FalseBenchmarkUpper': '''module
public import TetrahedronCover.BenchmarkPolynomials
open TetrahedronCover
open scoped BigOperators
example : (∑ j ∈ Finset.range 5000, benchmarkSummand8 (j : ℝ)) ≤
    (4999/10000 : ℝ) := by
  rw [benchmark_sum8]
  norm_num [benchmarkPrimitive8]
''',
            'DamagedTaylorIdentity': '''module
public import TetrahedronCover.InverseSqrt
open TetrahedronCover
example (z : ℝ) : taylor8 z =
    1-z/2+3*z^2/8-5*z^3/16+35*z^4/128-63*z^5/256+
      231*z^6/1024-429*z^7/2048+6436*z^8/32768 := by
  unfold taylor8
  ring
''',
        }
        for name, source in cases.items():
            path = BUILD / (name+'.lean')
            path.write_text(source)
            print('NEGATIVE CONTROL ' + name, flush=True)
            command = [lean, '-j', '1', '-M', str(args.memory_mb),
                       '-DmaxHeartbeats=4000000', '-DmaxRecDepth=10000', str(path)]
            result = run_checked(command, name, expect_rejection=True)
            result['source_sha256'] = hashlib.sha256(source.encode()).hexdigest()
            controls.append(result)
    report = dict(status='compiled', target=args.target, lean=version, mathlib_revision=revision,
                  upstream_revision=manifest['revision'], threads=1, lean_allocation_limit_mb=args.memory_mb,
                  resident_limit_mb=args.resident_mb,
                  timeout_per_module_seconds=args.module_seconds, host=platform.platform(),
                  modules_in_dependency_closure=len(visited), modules_compiled_this_run=len(records),
                  elapsed_seconds=round(time.monotonic()-started, 4),
                  child_max_rss=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  child_max_rss_unit='bytes' if sys.platform == 'darwin' else 'KiB', records=records,
                  checked_closure={module: state[module] for module in visited},
                  replay_records=replay_records, replay_driver_sha256=hashlib.sha256(replay_source.encode()).hexdigest(),
                  negative_controls=controls, axiom_audit=axiom_audit)
    (BUILD / 'last-build.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()
                      if k not in ('records', 'checked_closure', 'replay_records', 'negative_controls', 'axiom_audit')}), flush=True)

if __name__ == '__main__':
    main()
