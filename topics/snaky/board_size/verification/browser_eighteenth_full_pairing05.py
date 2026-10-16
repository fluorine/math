#!/usr/bin/env python3
"""Check the explicit31-pair full physical defense; no search or constructor imports."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

from check_repaired13_physical_matching import derive
from check_pairing import check, winning_sets


BASE = Path(__file__).resolve().parents[1]
ACCEPTED = 'verification/browser-seventeenth-composition05-01.json'
BROWSER = 'browser/05-eighteenth-final.txt'
PINS = {
    ACCEPTED: '2263c092bb013af533132927cffb76d76e536f2dfb0b38c10475276d4588d4a8',
    'verification/browser_seventeenth_composition05.py':
        'eb3d8b705f0e52cf55f04020a10d0097ac7150c7819520b7246ac82f316937b8',
    BROWSER: '58a32fc2329febfec52fe37755913b4352f7f8f70969e275399ca0f8a9a266b0',
    'verification/check_repaired13_physical_matching.py':
        '05bf0a9a7006fab493befd1bb1e5f1f38a3e749df0551b0e9bdb9bd63547987b',
    'breaker/check_pairing.py':
        'f24d5a389197f5010afc88036e0b849c3f31caadb60c142f29c1b3c684191056',
}
PAIRS = ((0,10),(2,12),(3,13),(4,15),(5,6),(7,9),(8,17),(16,27),(18,28),(19,26),
         (25,35),(39,49),(40,50),(41,51),(42,52),(53,54),(59,69),(60,80),(61,81),
         (62,72),(63,64),(65,95),(66,76),(68,78),(70,71),(73,93),(82,83),(85,86),
         (88,89),(90,91),(96,97))
UNPAIRED = (20,22,23,29,30,33,48,79,87,92,98,99)
OLD_PAIRS = ((12,22),(23,33),(42,52),(53,54),(30,41))
RELEASED = ((12,22),(23,33),(30,41))
ASSIGNMENT = (
    ((0,10),(1,)), ((2,12),(2,4)), ((3,13),(5,7)), ((4,15),(3,9)),
    ((5,6),(6,8,10,11)), ((7,9),(12,)), ((8,17),(15,16)),
    ((16,27),(14,22,25)), ((18,28),(21,26,27,28)), ((19,26),(24,)),
    ((25,35),(13,23)), ((39,49),(17,41)),
    ((40,50),(19,20,29,30,34,35,42,43)),
    ((41,51),(18,31,32,33,36,37,38,44,45,46,47)),
    ((59,69),(48,70)), ((60,80),(52,54)), ((61,81),(51,56,57,59)),
    ((62,72),(55,61,62,63)), ((63,64),(49,50,53,58,65,71,72,73,74,75)),
    ((65,95),(66,)), ((66,76),(39,67,77)), ((68,78),(40,68,69,76)),
    ((70,71),(78,79)), ((73,93),(60,)), ((82,83),(64,80,82,85,86,87)),
    ((85,86),(81,84,88,89,91,93,94)), ((88,89),(83,95,96)),
    ((90,91),(90,)), ((96,97),(92,)),
)
INCIDENCES = (
    ((12,22),(2,12,22,31,32,41),(2,12)),
    ((12,22),(3,12,13,22,32,42),(3,13)),
    ((12,22),(12,21,22,31,41,51),(41,51)),
    ((12,22),(12,22,32,41,42,51),(41,51)),
    ((23,33),(3,13,23,32,33,42),(3,13)),
    ((23,33),(23,32,33,42,52,62),(42,52)),
    ((30,41),(0,10,20,30,31,41),(0,10)),
    ((30,41),(10,20,30,40,41,51),(41,51)),
    ((30,41),(20,30,31,41,51,61),(41,51)),
    ((30,41),(30,40,41,51,61,71),(41,51)),
)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def audit(accepted, pairs=PAIRS, assignment=ASSIGNMENT, incidences=INCIDENCES, guard=lambda:None):
    binding = derive(accepted)
    maker, breaker = map(set, (binding['state']['maker'], binding['state']['breaker']))
    checked = check(10, pairs, maker, breaker)
    need(checked['placements'] == 432 and checked['live_placements'] == 127
         and checked['pairs'] == 31 and not checked['empty_board'], 'full conditional pairing dimensions differ')
    paired = {v for p in pairs for v in p}
    need(len(paired) == 62 and sorted(set(range(100))-maker-breaker-paired) == list(UNPAIRED),
         'fresh or unpaired cells differ')
    pairsets = set(map(frozenset, pairs))
    need(pairsets & set(map(frozenset, OLD_PAIRS)) == {frozenset((42,52)),frozenset((53,54))},
         'retained/released old pair accounting differs')
    edges = winning_sets(10); live = {e for e in edges if not e&breaker}
    old_live = {e for e in edges if not e&set(binding['original_state']['breaker'])}
    old_covered = {e for e in live if any(set(p) <= e for p in OLD_PAIRS)}
    unassigned = list(map(frozenset, accepted['repair']['unassigned_initial_targets']))
    need(len(old_live) == 194 and len(live) == 127 and len(old_live-live) == 67
         and len(old_covered) == 31 and len(unassigned) == len(set(unassigned)) == 96
         and set(unassigned) == live-old_covered
         and unassigned == sorted(unassigned, key=lambda e:tuple(sorted(e))), '96-target partition differs')
    need(unassigned[0] == frozenset((0,10,11,21,31,41))
         and unassigned[-1] == frozenset((88,89,95,96,97,98)), 'browser target indexing differs')
    assigned_indices = [i for _, indices in assignment for i in indices]
    need(sorted(assigned_indices) == list(range(1,97)), '96-target assignment is not exact once-only coverage')
    assigned = []
    for pair, indices in assignment:
        guard(); need(frozenset(pair) in pairsets, 'witness is not an installed pair')
        for i in indices:
            edge = unassigned[i-1]
            need(set(pair) <= edge, 'browser96 target witness is not contained')
            assigned.append(dict(index=i, target=sorted(edge), pair=list(pair)))
    expected = {(tuple(p),tuple(sorted(e))) for p in RELEASED for e in live if set(p) <= e}
    actual = {(tuple(p),tuple(e)) for p,e,_ in incidences}
    need(len(incidences) == len(actual) == len(expected) == 10 and actual == expected,
         'released-pair incidence table is incomplete or duplicated')
    released = []
    for old, edge, new in incidences:
        guard(); need(frozenset(new) in pairsets and set(new) <= set(edge), 'released-pair replacement misses target')
        released.append(dict(released_pair=list(old), target=list(edge), new_pair=list(new)))
    coverage = []
    for e in sorted(edges, key=lambda t:tuple(sorted(t))):
        guard()
        hits = sorted(e&breaker)
        witnesses = sorted(sorted(p) for p in pairsets if p <= e)
        need(bool(hits) or bool(witnesses), 'full physical coverage failed')
        coverage.append(dict(target=sorted(e), breaker_hits=hits, pairs=witnesses))
    return dict(status='verified_full_conditional_repaired13_pairing', independent_pairing_check=checked,
        original_state=binding['original_state'], actual_prefix=binding['actual_prefix'], physical_state=binding['state'],
        certificate=dict(schema='snaky-static-pairing-v1', size=10, maker=sorted(maker),
                         breaker=sorted(breaker), pairs=[list(p) for p in pairs]),
        paired_cells=62, unpaired_cells=list(UNPAIRED), initial_live_targets=194,
        newly_blocked_targets=67, previously_pair_covered_live_targets=31, unassigned_live_targets=96,
        unassigned_witnesses=sorted(assigned, key=lambda r:r['index']), released_pair_incidences=released,
        all432_coverage=coverage, full_conditional_game_leaf=True, upstream_root_proved=False, empty10_result=False)


def controls(accepted, guard):
    cases = [
        ('occupied_pair_endpoint', lambda:audit(accepted, pairs=((11,10),)+PAIRS[1:], guard=guard)),
        ('overlapping_pair_endpoints', lambda:audit(accepted, pairs=PAIRS+((0,20),), guard=guard)),
        ('omitted_essential_pair', lambda:audit(accepted, pairs=PAIRS[1:], guard=guard)),
        ('omitted96_target_index', lambda:audit(accepted, assignment=ASSIGNMENT[1:], guard=guard)),
        ('wrong96_target_pair', lambda:audit(accepted, assignment=(((2,12),(1,)),)+ASSIGNMENT[1:], guard=guard)),
        ('missing_released_incidence', lambda:audit(accepted, incidences=INCIDENCES[:-1], guard=guard)),
        ('wrong_released_witness', lambda:audit(accepted,
            incidences=(INCIDENCES[0][:2]+((42,52),),)+INCIDENCES[1:], guard=guard)),
    ]
    results = []
    for name, operation in cases:
        guard()
        try:
            operation()
        except ValueError as error:
            results.append(dict(name=name, rejected=True, reason=str(error)))
        else:
            raise ValueError('negative control accepted: '+name)
    return results


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(argv)
    need(not args.output.exists(), 'fresh output required')
    cpu, wall = time.process_time(), time.monotonic()
    def guard():
        if time.process_time()-cpu > 4 or time.monotonic()-wall > 25:
            raise TimeoutError('literal_pairing_audit_resource_limit')
    report = dict(schema='snaky-browser-eighteenth-full-pairing05-audit-v1', status='unknown',
        checker_sha256=sha(Path(__file__).read_bytes()), input_sha256=PINS,
        scope='Full physical Breaker pairing leaf at the exact repaired13M/13B state, not an upstream or empty10 defense.')
    try:
        for name, expected in PINS.items():
            guard(); need(sha((BASE/name).read_bytes()) == expected, 'changed input: '+name)
        accepted = json.loads((BASE/ACCEPTED).read_text())
        report.update(audit(accepted, guard=guard), negative_controls=controls(accepted, guard))
    except TimeoutError as error:
        report.update(status='unknown', reason=str(error))
    except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
        report.update(status='failed', reason=f'{type(error).__name__}: {error}')
    report.update(created_utc=datetime.now(timezone.utc).isoformat(), process_cpu_seconds=time.process_time()-cpu,
                  elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        stream.write(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:report.get(k) for k in ('status', 'reason', 'independent_pairing_check',
                                               'process_cpu_seconds', 'elapsed_seconds')}))
    return 0 if report['status'] == 'verified_full_conditional_repaired13_pairing' else 2


if __name__ == '__main__':
    raise SystemExit(main())
