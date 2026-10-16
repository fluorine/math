#!/usr/bin/env python3
"""Independent exact-S11 static matching formula and complete-model check.

Rebuilds the full physical state and432 literal targets. It imports only
already reviewed independent pairing/formula helpers, never the constructor.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys
import time

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE/'breaker'))
from check_pairing import check, winning_sets
from check_repaired13_physical_matching import expected_formula, model_pairs

ACCEPTED = 'verification/post-m31-joint-matching-result-01.json'
CERTIFICATE = 'verification/post-m31-joint-matching-result-01.pairing.json'
CONSTRUCTOR = 'breaker/upstream11_physical_matching.py'
ENCODER_PINS = {
    ACCEPTED: '69df417b3a66aebb14b6203fec1355d03c740ae9165b08fc3fd2147526981c30',
    CERTIFICATE: '5d57788fd23e96a8e46a16cfd83d723dadbe75f90f2a2089e0f486854906b2bf',
    'verification/check_post_m31_joint_matching.py':
        'a0bcfc9c88a36224f16817a4442528ce2da69b3253b1ae6090b328d98ede8bc6',
    'breaker/static_pairing.py':
        '6132d522f6a72ae7f8ec2f4f1714c7a5f31335dba9c4f44b59020ce9fcb39266',
    'breaker/hypergraph.py':
        '19aa54842d59e5b1c0da5f0277c1ad20096d04966241b1eaad7551ff23614faa',
    'breaker/check_pairing.py':
        'f24d5a389197f5010afc88036e0b849c3f31caadb60c142f29c1b3c684191056',
}
PINS = dict(ENCODER_PINS, **{
    CONSTRUCTOR: '6d9cf0ac8c319d12ac0d168a86238e1f8f79c8e4dbda2cd113f4e19d1bb0bca0',
    'verification/check_repaired13_physical_matching.py':
        '05bf0a9a7006fab493befd1bb1e5f1f38a3e749df0551b0e9bdb9bd63547987b',
    'breaker/adaptive_run.py':
        'dd59dc64f76c0e93f5b963ef0e6a444e74ceb4003d126c3f42937430affb60aa',
    'breaker/cpu_exec.py':
        '0819f781e2cd2e3ce29e499ecacca46373219d8ab7cbe263c0a59a91cbea6278',
})
M0 = frozenset((37,44,45,46,47,57,67,75,84))
B0 = frozenset((34,36,38,55,56,58,74,77,94))
GEOMETRY_SHA = '06b3a966ff46af6b36a59e88f562e985f752690959a4a1f27dd17a657ca282ed'
PYTHON = '/opt/homebrew/Cellar/python@3.12/3.12.12_2/Frameworks/Python.framework/Versions/3.12/bin/python3.12'
PYTHON_SHA = '51041dcef59a872d4e411dfd26f6264f70bd67294bebbe52a707490726f0d1a6'
Z3 = '/opt/homebrew/bin/z3'
Z3_SHA = 'ae6c8df33db9c9ae9a80b6044e77cd66529a141d8b25f0620f1e89b409594f48'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dependency_pins(accepted):
    pins = dict(accepted['source_sha256'])
    earlier = json.loads((BASE/'verification/browser-nineteenth-physical12-05-01.json').read_text())
    for name, digest in earlier['input_sha256'].items():
        need(name not in pins or pins[name] == digest, 'contradictory accepted dependency')
        pins[name] = digest
    for name, digest in pins.items():
        need(sha((BASE/name).read_bytes()) == digest, 'changed accepted dependency: '+name)
    return pins


def derive(accepted):
    original = dict(maker=sorted(M0), breaker=sorted(B0), turn='Maker')
    prefix = [dict(maker=11,breaker=14), dict(maker=21,breaker=43)]
    need(accepted['status'] == 'verified_conditional_postM31_reply_pairing'
         and accepted['checker_sha256'] == PINS['verification/check_post_m31_joint_matching.py']
         and accepted['breaker_reply'] == 41
         and accepted['binding']['original_state'] == original
         and accepted['binding']['completed_prefix'] == prefix
         and accepted['binding']['pending_Maker_claim'] == 31,
         'accepted physical source or actual prefix differs')
    edges = sorted(winning_sets(10), key=lambda e:tuple(sorted(e)))
    need(len(edges) == 432 and sha((json.dumps([sorted(e) for e in edges],separators=(',',':'))+'\n').encode())
         == GEOMETRY_SHA, 'independent literal geometry differs')
    maker, breaker = set(M0), set(B0)
    for row in prefix:
        u,v = row['maker'],row['breaker']
        need(u not in maker|breaker and v not in maker|breaker|{u}, 'prefix claim was not fresh')
        maker.add(u); need(not any(e <= maker for e in edges), 'prefix continued after a Maker win')
        breaker.add(v)
    state = dict(maker=sorted(maker), breaker=sorted(breaker), turn='Maker')
    free = set(range(100))-maker-breaker
    need(len(maker) == len(breaker) == 11 and len(free) == 78 and {31,41} <= free,
         'not the exact S11 state')
    successor = dict(maker=sorted(maker|{31}), breaker=sorted(breaker|{41}), turn='Maker')
    pending = dict(maker=successor['maker'], breaker=state['breaker'], turn='Breaker')
    need(not any(e <= maker|{31} for e in edges), 'M31 completed a physical Snaky')
    cert = accepted['certificate']
    need(accepted['state_after_reply'] == successor and accepted['binding']['state'] == pending
         and cert['schema'] == 'snaky-static-pairing-v1' and cert['size'] == 10
         and cert['maker'] == successor['maker'] and cert['breaker'] == successor['breaker'],
         'accepted successor or reply colors differ')
    old_check = check(10, cert['pairs'], successor['maker'], successor['breaker'])
    need(old_check == accepted['independent_pairing_check'] and old_check['live_placements'] == 119
         and old_check['pairs'] == 35, 'accepted35-pair full physical leaf differs')
    old_pairs = list(map(frozenset,cert['pairs']))
    live = [e for e in edges if not e&breaker]
    missing = [e for e in live if not any(p <= e for p in old_pairs)]
    need(all(41 in e for e in missing), 'old-pair missing target does not contain removed B41')
    rows = [dict(physical_target=sorted(e),maker_owned=sorted(e&maker),required_free=sorted(e-maker)) for e in live]
    residuals = [tuple(row['required_free']) for row in rows]
    need(all(set(t) <= free and len(t) >= 1 for t in residuals), 'invalid physical residual')
    return dict(size=10,coordinate_convention='cell=10*y+x, zero-based',accepted_successor=successor,
        removed_claims=dict(maker=[31],breaker=[41]), original_state=original, actual_prefix=prefix,
        state=state,free_cells=sorted(free),literal_target_count=432,literal_target_sha256=GEOMETRY_SHA,
        live_target_count=len(live),physical_targets=rows,distinct_residual_count=len(set(residuals)),
        residual_size_counts={str(k):v for k,v in sorted(Counter(map(len,residuals)).items())},
        two_cell_requirements=sorted(list(t) for t in residuals if len(t) == 2),
        previous35_diagnostic=dict(pairs=cert['pairs'],still_disjoint_and_fresh=True,
            covered_live_targets=len(live)-len(missing),missing_targets=[sorted(e) for e in missing],
            all_missing_contain41=True),fixed_pairs=[],forbidden_pairs=[],projected_away_cells=[])


def check_instance(instance, formula, accepted, dependencies):
    binding = derive(accepted)
    text,pairs = expected_formula(binding)
    need(instance['schema'] == 'snaky-upstream11-full-matching-instance-v1'
         and instance['status'] == 'exported' and instance['source_sha256'] == PINS[CONSTRUCTOR]
         and instance['input_sha256'] == ENCODER_PINS
         and instance['accepted_dependencies_sha256'] == dependencies and instance['binding'] == binding
         and instance['query_started'] is False and instance['independent_acceptance'] is None,
         'instance binding, restrictions, or provenance differ')
    incidence = Counter(v for p in pairs for v in p)
    need(formula == text and instance['formula_sha256'] == sha(text.encode('ascii'))
         and instance['pair_variables'] == [list(p) for p in pairs]
         and instance['pair_variable_count'] == len(pairs)
         and instance['nontrivial_cell_capacities'] == sum(n>1 for n in incidence.values()),
         'unrestricted static formula or variable map differs')
    return binding,pairs


def classify(output, exit_code, finished, variables, binding):
    if not finished or exit_code != 0:
        return dict(status='UNKNOWN',reason='Solver did not finish normally within the guard.',certificate=None)
    answers = re.findall(r'^(sat|unsat|unknown)\s*$',output,re.MULTILINE)
    need(len(answers) == 1 and not re.search(r'\(error\b|\bERROR:',output),'invalid solver answer')
    if answers[0] == 'unknown':
        return dict(status='UNKNOWN',reason='Solver reported unknown.',certificate=None)
    if answers[0] == 'unsat':
        return dict(status='unproved_static_matching_unsat_observation',certificate=None,
            reason='Restricted static matching class only; no checked UNSAT proof or adaptive-game conclusion.')
    pairs = model_pairs(output,variables)
    state = binding['state']; checked = check(10,pairs,state['maker'],state['breaker'])
    need(checked['placements'] == 432 and checked['live_placements'] == binding['live_target_count']
         and not checked['empty_board'],'full physical pairing dimensions differ')
    cert = dict(schema='snaky-static-pairing-v1',size=10,maker=state['maker'],breaker=state['breaker'],
                pairs=[list(p) for p in pairs])
    return dict(status='verified_conditional_upstream11_full_physical_pairing',
                independent_pairing_check=checked,certificate=cert)


def controls(instance, formula, accepted, dependencies):
    outcomes = []
    def reject(name, operation):
        try: operation()
        except ValueError as error: outcomes.append(dict(name=name,rejected=True,reason=str(error)))
        else: raise ValueError('negative control accepted: '+name)
    altered = deepcopy(accepted); altered['breaker_reply'] = 24
    reject('B24_instead_of_accepted_B41',lambda:derive(altered))
    altered = deepcopy(accepted); altered['binding']['original_state']['breaker'].remove(34)
    reject('lost_old_Breaker_color',lambda:derive(altered))
    for key,value in (('removed_claims',dict(maker=[21],breaker=[41])),
                      ('fixed_pairs',[[1,30]]),('projected_away_cells',[41])):
        altered = deepcopy(instance); altered['binding'][key] = value
        reject('altered_'+key,lambda a=altered:check_instance(a,formula,accepted,dependencies))
    altered = deepcopy(instance); altered['binding']['physical_targets'].pop()
    reject('missing_full_live_target',lambda:check_instance(altered,formula,accepted,dependencies))
    for name,start in (('missing_target_clause','(assert (or '),('missing_cell_capacity','(assert ((_ at-most 1)')):
        lines = formula.splitlines(); del lines[next(i for i,line in enumerate(lines) if line.startswith(start))]
        reject(name,lambda lines=lines:check_instance(instance,'\n'.join(lines)+'\n',accepted,dependencies))
    variables = [tuple(p) for p in instance['pair_variables']]
    reject('partial_Boolean_model',lambda:model_pairs('sat\n(define-fun p_0_1 () Bool true)\n',variables))
    false_model = 'sat\n(\n'+'\n'.join(f'(define-fun p_{a}_{b} () Bool false)' for a,b in variables)+'\n)\n'
    reject('SAT_without_full_physical_cover',lambda:classify(false_model,0,True,variables,instance['binding']))
    need(classify('sat\n',-9,False,variables,instance['binding'])['status'] == 'UNKNOWN','cutoff accepted')
    outcomes.append(dict(name='cutoff_stays_UNKNOWN',passed=True))
    need(classify('unsat\n',0,True,variables,instance['binding'])['status'] == 'unproved_static_matching_unsat_observation',
         'unproved UNSAT became a game claim')
    outcomes.append(dict(name='UNSAT_stays_restricted_observation',passed=True))
    return outcomes


def expected_command(formula):
    return ['/usr/bin/nice','-n','19',PYTHON,'-B',str(BASE/'breaker/cpu_exec.py'),'--cpu-seconds','30','--',
        Z3,'-smt2','-model','-st','-memory:150','smt.threads=1','sat.threads=1',
        'parallel.enable=false','sat.random_seed=0',str(formula.resolve())]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True); parser.add_argument('--input-sha256',required=True)
    parser.add_argument('--formula',type=Path,required=True); parser.add_argument('--controls',action='store_true')
    parser.add_argument('--guard',type=Path); parser.add_argument('--guard-sha256')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args(argv)
    need(not args.output.exists() and bool(args.guard) == bool(args.guard_sha256),'fresh output and complete guard binding required')
    cpu,wall = time.process_time(),time.monotonic()
    report = dict(schema='snaky-upstream11-full-matching-independent-v1',status='rejected',
        checker_sha256=sha(Path(__file__).read_bytes()),source_sha256=PINS,instance_sha256=args.input_sha256,
        scope='Exact11M/11B physical Maker turn after M11/B14,M21/B43. No upstream S9 or empty10 claim.')
    try:
        for name,digest in PINS.items(): need(sha((BASE/name).read_bytes()) == digest,'changed input: '+name)
        accepted = json.loads((BASE/ACCEPTED).read_text())
        need(json.loads((BASE/CERTIFICATE).read_text()) == accepted['certificate'],'accepted certificate differs')
        dependencies = dependency_pins(accepted)
        need(sha(args.input.read_bytes()) == args.input_sha256,'instance changed')
        instance = json.loads(args.input.read_text()); formula = args.formula.read_text()
        need(Path(instance['formula_path']).resolve() == args.formula.resolve(),'formula path differs')
        binding,variables = check_instance(instance,formula,accepted,dependencies)
        report.update(status='verified_upstream11_unrestricted_matching_encoding',binding=binding,
            accepted_dependencies_sha256=dependencies,formula_sha256=instance['formula_sha256'],
            pair_variable_count=len(variables),solver_started=False)
        if args.controls: report['focused_controls'] = controls(instance,formula,accepted,dependencies)
        if args.guard:
            need(sha(args.guard.read_bytes()) == args.guard_sha256 and sha(Path(Z3).read_bytes()) == Z3_SHA
                 and sha(Path(PYTHON).read_bytes()) == PYTHON_SHA,'guard or runtime binary differs')
            guard = json.loads(args.guard.read_text())
            need(guard['schema'] == 'snaky-external-run-guard-v1'
                 and guard['guard_sha256'] == PINS['breaker/adaptive_run.py']
                 and guard['command'] == expected_command(args.formula)
                 and guard['wall_seconds'] == 120 and guard['rss_cap_bytes'] == 200*1024**2,
                 'wrong direct solver execution')
            output = Path(guard['log']).read_text() if guard.get('log') else ''
            outcome = classify(output,guard.get('exit_code'),guard['status'] == 'finished',variables,binding)
            report.update(outcome,solver_started=bool(guard.get('pid')),solver_guard_sha256=args.guard_sha256,
                solver_output_sha256=sha(output.encode()),solver_pid=guard.get('pid'),solver_exit_code=guard.get('exit_code'),
                solver_guard_status=guard['status'])
            if outcome.get('certificate'):
                path = args.output.with_suffix('.pairing.json'); need(not path.exists(),'fresh certificate path required')
                with path.open('x') as stream: stream.write(json.dumps(outcome['certificate'],indent=2)+'\n')
                report['certificate_path'] = str(path.resolve())
    except (ValueError,KeyError,TypeError,IndexError,OSError,UnicodeError) as error:
        report.update(status='rejected',reason=f'{type(error).__name__}: {error}')
    report.update(created_utc=datetime.now(timezone.utc).isoformat(),process_cpu_seconds=time.process_time()-cpu,
                  elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x') as stream: stream.write(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:report.get(k) for k in ('status','reason','pair_variable_count',
        'independent_pairing_check','process_cpu_seconds','elapsed_seconds')}))
    return int(report['status'] == 'rejected')


if __name__ == '__main__':
    raise SystemExit(main())
