#!/usr/bin/env python3
"""Independently bind/check the unrestricted repaired13+13 matching experiment.

Imports only the existing independent full pairing checker, never the encoder
or its geometry helpers. An UNSAT banner remains an unproved observation.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import re
import sys
import time

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE/'breaker'))
from check_pairing import check, winning_sets


ACCEPTED = 'verification/browser-seventeenth-composition05-01.json'
ENCODER_PINS = {
    ACCEPTED: '2263c092bb013af533132927cffb76d76e536f2dfb0b38c10475276d4588d4a8',
    'verification/browser_seventeenth_composition05.py':
        'eb3d8b705f0e52cf55f04020a10d0097ac7150c7819520b7246ac82f316937b8',
    'breaker/static_pairing.py':
        '6132d522f6a72ae7f8ec2f4f1714c7a5f31335dba9c4f44b59020ce9fcb39266',
    'breaker/hypergraph.py':
        '19aa54842d59e5b1c0da5f0277c1ad20096d04966241b1eaad7551ff23614faa',
}
CONSTRUCTOR = 'breaker/repaired13_physical_matching.py'
PINS = dict(ENCODER_PINS, **{
    CONSTRUCTOR: 'fc867e90d5b82c8aee32ac821847b2f0a76dd53e93ef59accda078967fbd42f3',
    'breaker/check_pairing.py':
        'f24d5a389197f5010afc88036e0b849c3f31caadb60c142f29c1b3c684191056',
    'breaker/adaptive_run.py':
        'dd59dc64f76c0e93f5b963ef0e6a444e74ceb4003d126c3f42937430affb60aa',
    'breaker/cpu_exec.py':
        '0819f781e2cd2e3ce29e499ecacca46373219d8ab7cbe263c0a59a91cbea6278',
})
PYTHON = '/opt/homebrew/bin/python3.12'
Z3 = '/opt/homebrew/bin/z3'
Z3_SHA = 'ae6c8df33db9c9ae9a80b6044e77cd66529a141d8b25f0620f1e89b409594f48'
M0 = frozenset((37, 44, 45, 46, 47, 57, 67, 75, 84))
B0 = frozenset((34, 36, 38, 55, 56, 58, 74, 77, 94))
PREFIX = ((11, 14), (21, 43), (31, 24), (32, 1))
GEOMETRY_SHA = '06b3a966ff46af6b36a59e88f562e985f752690959a4a1f27dd17a657ca282ed'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def derive(accepted):
    original = dict(maker=sorted(M0), breaker=sorted(B0), turn='Maker')
    need(accepted['status'] == 'verified_conditional_K19_dispatcher_loss_and_guarded_repair'
         and accepted['checker_sha256'] == PINS['verification/browser_seventeenth_composition05.py']
         and accepted['initial_physical_state'] == original, 'accepted physical source differs')
    edges = sorted(winning_sets(10), key=lambda e:tuple(sorted(e)))
    raw = (json.dumps([sorted(e) for e in edges], separators=(',', ':'))+'\n').encode()
    need(len(edges) == 432 and sha(raw) == GEOMETRY_SHA, 'independent literal geometry differs')
    maker, breaker, history = set(M0), set(B0), []
    for i, (u, v) in enumerate(PREFIX):
        row = accepted['prescribed_prefix'][i]
        need(row['maker'] == u and row['reply'] == (v if i != 3 else 33)
             and row['before']['maker'] == sorted(maker) and row['before']['breaker'] == sorted(breaker),
             'bound prefix differs')
        need(u not in maker | breaker and v not in maker | breaker | {u}, 'prefix is not fresh')
        maker.add(u)
        need(not any(e <= maker for e in edges), 'immediate physical Maker win in prefix')
        breaker.add(v); history.append(dict(maker=u, breaker=v))
    repair = accepted['repair']
    need(len(maker) == len(breaker) == 13 and not maker & breaker
         and repair['maker'] == sorted(maker) and repair['breaker'] == sorted(breaker)
         and repair['actual_reply'] == 1 and repair['fictitious_reply33'] is False
         and repair['turn'] == 'Maker', 'not the actual repaired13+13 state')
    free = set(range(100))-maker-breaker
    rows = [dict(physical_target=sorted(e), maker_owned=sorted(e&maker),
                 required_free=sorted(e-maker)) for e in edges if not e&breaker]
    residuals = [tuple(row['required_free']) for row in rows]
    need(len(free) == 74 and len(rows) == len(set(residuals)) == 127
         and all(set(t) <= free and len(t) >= 2 for t in residuals), 'full physical target family differs')
    binding = dict(size=10, coordinate_convention='cell=10*y+x, zero-based', original_state=original,
        actual_prefix=history, state=dict(maker=sorted(maker), breaker=sorted(breaker), turn='Maker'),
        free_cells=sorted(free), literal_target_count=432, literal_target_sha256=GEOMETRY_SHA,
        live_target_count=127, physical_targets=rows, distinct_residual_count=127,
        residual_size_counts={str(k):v for k,v in sorted(Counter(map(len, residuals)).items())},
        fixed_pairs=[], forbidden_pairs=[], projected_away_cells=[],
        two_cell_requirements=sorted(list(e) for e in residuals if len(e) == 2))
    return binding


def expected_formula(binding):
    """Literal independent clause reconstruction; no call to static_pairing.encode."""
    residuals = [row['required_free'] for row in binding['physical_targets']]
    pairs = sorted({p for target in residuals for p in combinations(target, 2)})
    lines = ['(set-logic QF_FD)', '(set-option :produce-models true)']
    lines += [f'(declare-fun p_{a}_{b} () Bool)' for a,b in pairs]
    for cell in range(100):
        names = [f'p_{a}_{b}' for a,b in pairs if cell in (a,b)]
        if len(names) > 1:
            lines.append('(assert ((_ at-most 1) '+' '.join(names)+'))')
    for target in residuals:
        names = [f'p_{a}_{b}' for a,b in combinations(target, 2)]
        lines.append('(assert (or '+' '.join(names)+'))')
    lines.append('(check-sat)')
    return '\n'.join(lines)+'\n', pairs


def check_instance(instance, formula, accepted):
    binding = derive(accepted)
    text, pairs = expected_formula(binding)
    need(instance['schema'] == 'snaky-repaired13-full-matching-instance-v1'
         and instance['status'] == 'exported' and instance['source_sha256'] == PINS[CONSTRUCTOR]
         and instance['input_sha256'] == ENCODER_PINS and instance['binding'] == binding
         and instance['query_started'] is False and instance['independent_acceptance'] is None,
         'instance binding or source differs')
    need(formula == text and sha(formula.encode('ascii')) == instance['formula_sha256']
         and instance['pair_variables'] == [list(p) for p in pairs]
         and instance['pair_variable_count'] == len(pairs) == 531
         and instance['nontrivial_cell_capacities'] == 73, 'formula, variables or capacities differ')
    return binding, pairs


def model_pairs(output, variables):
    entries = re.findall(r'\(define-fun\s+p_(\d+)_(\d+)\s+\(\)\s+Bool\s+(true|false)\s*\)', output)
    keys = [(int(a), int(b)) for a,b,_ in entries]
    need(len(keys) == len(set(keys)) == len(variables) and set(keys) == set(variables)
         and len(re.findall(r'\(define-fun\s+', output)) == len(keys),
         'truncated, duplicate or unexpected model definitions')
    return sorted((int(a), int(b)) for a,b,value in entries if value == 'true')


def classify(output, exit_code, finished, variables, binding):
    if not finished or exit_code != 0:
        return dict(status='unknown', reason='Solver did not finish normally within its guard.', certificate=None)
    answers = re.findall(r'^(sat|unsat|unknown)\s*$', output, re.MULTILINE)
    need(len(answers) == 1 and not re.search(r'\(error\b|\bERROR:', output), 'missing, mixed or erroneous solver answer')
    if answers[0] == 'unsat':
        return dict(status='unproved_static_matching_unsat_observation', certificate=None,
                    reason='No independent UNSAT proof; adaptive defense remains undecided.')
    if answers[0] == 'unknown':
        return dict(status='unknown', reason='Solver reported unknown.', certificate=None)
    pairs = model_pairs(output, variables)
    state = binding['state']
    result = check(10, pairs, state['maker'], state['breaker'])
    need(result['placements'] == 432 and result['live_placements'] == 127 and result['empty_board'] is False,
         'independent full pairing dimensions differ')
    certificate = dict(schema='snaky-static-pairing-v1', size=10, maker=state['maker'],
                       breaker=state['breaker'], pairs=[list(p) for p in pairs])
    return dict(status='verified_conditional_repaired13_full_physical_pairing',
                independent_pairing_check=result, certificate=certificate)


def expected_command(formula):
    return ['nice', '-n', '19', PYTHON, '-B', str(BASE/'breaker/cpu_exec.py'), '--cpu-seconds', '30', '--',
            Z3, '-smt2', '-model', '-st', '-memory:150', 'smt.threads=1', 'sat.threads=1',
            'parallel.enable=false', 'sat.random_seed=0', str(formula.resolve())]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, required=True); ap.add_argument('--input-sha256', required=True)
    ap.add_argument('--formula', type=Path, required=True)
    ap.add_argument('--guard', type=Path, required=True); ap.add_argument('--guard-sha256', required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(argv)
    need(not args.output.exists(), 'fresh audit output required')
    cpu, wall = time.process_time(), time.monotonic()
    report = dict(schema='snaky-repaired13-full-matching-independent-v1', status='failed',
        checker_sha256=sha(Path(__file__).read_bytes()), source_sha256=PINS,
        instance_sha256=args.input_sha256, guard_sha256=args.guard_sha256,
        scope='Only the exact repaired13M/13B physical Maker turn; no forced upstream or empty10 result.')
    try:
        for name, expected in PINS.items():
            need(sha((BASE/name).read_bytes()) == expected, 'changed source: '+name)
        need(sha(Path(Z3).read_bytes()) == Z3_SHA, 'changed solver binary')
        need(sha(args.input.read_bytes()) == args.input_sha256 and sha(args.guard.read_bytes()) == args.guard_sha256,
             'changed instance or execution guard')
        source = json.loads(args.input.read_text()); guard = json.loads(args.guard.read_text())
        binding, pairs = check_instance(source, args.formula.read_text(), json.loads((BASE/ACCEPTED).read_text()))
        need(Path(source['formula_path']).resolve() == args.formula.resolve()
             and guard['schema'] == 'snaky-external-run-guard-v1'
             and guard['guard_sha256'] == PINS['breaker/adaptive_run.py']
             and guard['command'] == expected_command(args.formula)
             and guard['wall_seconds'] == 120 and guard['rss_cap_bytes'] == 200*1024**2,
             'wrong bounded direct solver execution')
        log = Path(guard['log']); raw = log.read_bytes()
        report.update(binding=binding, formula_sha256=source['formula_sha256'], solver_binary_sha256=Z3_SHA,
                      solver_log=str(log), solver_log_sha256=sha(raw), solver_guard=guard)
        report.update(classify(raw.decode(), guard['exit_code'], guard['status'] == 'finished', pairs, binding))
    except (ValueError, KeyError, TypeError, IndexError, OSError, UnicodeError) as exc:
        report.update(status='failed', reason=f'{type(exc).__name__}: {exc}')
    report.update(created_utc=datetime.now(timezone.utc).isoformat(), process_cpu_seconds=time.process_time()-cpu,
                  elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        stream.write(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:report.get(k) for k in ('status', 'reason', 'independent_pairing_check',
                                               'process_cpu_seconds', 'elapsed_seconds')}))
    return 2 if report['status'] == 'failed' else 0


if __name__ == '__main__':
    raise SystemExit(main())
