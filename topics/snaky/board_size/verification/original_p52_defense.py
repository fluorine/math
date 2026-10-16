#!/usr/bin/env python3
"""Finite full-target audit of the proposed original 11+11 P52 defense.

Reuses frozen independent geometry and matching validators, not a constructor.
All exterior histories are checked target by target; disjoint consumed pairs
cannot affect that target or the pristine six-cell reserved domain.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
from itertools import product
import json
from pathlib import Path
import time

from continued_endpoint_defenses import literal_targets, matching, local_table, R, GAMMA, ROWS

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/05-twentyfourth-final.txt': 'a88958d771391867ec192d388ca6f709ad70c9d198afa93fee93b3f944b404f5',
    'browser/05-twentyfourth-final-main.txt': '29c714362a9554d4a65610a0e43665905cc82ebd69248acd7b27ed5a2e4e12f0',
    'verification/continued_endpoint_defenses.py': 'cee9f08d63d4a0e8a28c18967da1917504d2e975a95b7310aa43cdf1c26ed187',
    'verification/browser_twentyfirst_independent05.json': '56d03252b70a863dd35137507b7e594e0d62af0f05854365a814aa73ab5ef45b',
}
M = frozenset((32,37,43,44,45,46,47,57,67,75,84))
B = frozenset((33,34,36,38,52,55,56,58,74,77,94))
Q = ((3,4),(5,6),(7,8),(10,20),(11,21),(12,22),(13,14),(15,25),
     (23,24),(29,49),(30,40),(31,42),(41,50),(51,61),(53,54),(59,79),
     (60,80),(62,72),(63,73),(64,65),(66,76),(68,78),(70,71),(81,91),
     (82,83),(85,86),(88,89),(92,93),(95,96))
FILL = ((0,1),(2,9),(19,35),(39,48),(69,87),(90,97),(98,99))
V = frozenset(range(100))


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def bind(state):
    need(state == dict(maker=sorted(M), breaker=sorted(B), turn='Maker'),
         'wrong original full ownership')
    need(len(M) == len(B) == 11 and not M & B, 'bad original counts')


def coverage(edges, pairs, breaker, guards=GAMMA):
    rows = []
    for e in edges:
        if e & breaker:
            continue
        ps = [sorted(p) for p in pairs if p <= e]
        gs = [sorted(g) for g in guards if g <= e]
        need(ps or gs, 'unprotected full target '+str(sorted(e)))
        rows.append(dict(target=sorted(e), exterior_pairs=ps, reserved_guards=gs))
    return rows


def audit(state, edges, tick):
    bind(state); local_table(ROWS)
    free = V-M-B
    need(len(free) == 78 and R <= free, 'wrong fresh inventory')
    cover = matching(Q, free-R)
    outer = matching(Q+FILL, free-R, free-R)
    need(len(cover) == 29 and len(outer) == 36, 'wrong pair counts')
    ledger = coverage(edges, cover, B)
    live = tuple(e for e in edges if not e & B)
    entries = []
    for u in sorted(free):
        tick()
        need(not any(e <= M|{u} for e in live), 'first Maker claim wins')
        if u in R:
            v, raw = ROWS[u]
            local = matching(raw, R-{u,v}, R-{u,v})
            pairs = matching(tuple(tuple(p) for p in outer+local), free-{u,v}, free-{u,v})
            surviving = [e for e in live if v not in e]
            need(all(any(p <= e for p in pairs) for e in surviving), 'switch leaves a full target unprotected')
            action = dict(kind='switch', pairs=[sorted(p) for p in pairs], live_targets=len(surviving))
        else:
            pair = next(p for p in outer if u in p)
            v = next(iter(pair-{u}))
            action = dict(kind='mate_and_wait')
        need(v in free-{u}, 'reply not physically fresh')
        entries.append(dict(maker=u, breaker=v, **action))
    # Enumerate every orientation of the outside pairs touching each target.
    # Unmentioned consumed pairs are disjoint from that target and R. Their
    # possible ownership cannot invalidate a target's fresh covering pair.
    histories = blocked = switches = 0
    digest = hashlib.sha256()
    for e in live:
        relevant = [tuple(sorted(p)) for p in outer if p & e]
        for choices in product(range(3), repeat=len(relevant)):
            tick(); hm, hb = set(M), set(B)
            for pair, choice in zip(relevant, choices):
                if choice:
                    hm.add(pair[choice-1]); hb.add(pair[2-choice])
            need(M <= hm and B <= hb and not hm & hb and not R & (hm|hb), 'lost physical history')
            histories += 1; digest.update(bytes(sorted(e))+bytes(choices))
            if e & hb:
                blocked += 1
                continue
            need(not e <= hm, 'waiting target completed')
            # A waiting exterior move changes a pair from untouched to consumed.
            # Before its actual reply it must not complete e either.
            for pair in relevant:
                if not set(pair) & (hm|hb):
                    for u in pair:
                        need(not e <= hm|{u}, 'exterior claim wins before mate')
            for u, (v, raw) in ROWS.items():
                need(not e <= hm|{u}, 'reserved entry wins before reply')
                if v not in e:
                    available = V-hm-hb-{u,v}
                    need(any(p <= e and p <= available for p in outer+tuple(map(frozenset,raw))),
                         'outside history invalidates switch')
                switches += 1
    return dict(state=state, fresh_cells=78, live_targets=len(live),
        covering_pairs=Q, outside_perfect_matching=Q+FILL,
        coverage_ledger=ledger, first_entries=entries,
        targetwise_histories=histories, blocked_histories=blocked,
        live_history_switch_checks=switches, history_sha256=digest.hexdigest(),
        exhaustion=[dict(outside_pairs_left=r,before_switch_free=2*r+6,
                         after_switch_free=2*r+4) for r in range(37)])


def controls(state, edges):
    names = []
    def reject(name, fn):
        try:
            fn()
        except ValueError:
            names.append(name)
        else:
            raise ValueError('control accepted '+name)
    for color in ('maker','breaker'):
        changed = deepcopy(state); changed[color].pop()
        reject('lost_old_'+color, lambda: bind(changed))
    wrong = deepcopy(state); wrong['breaker'].remove(52); wrong['breaker'].append(53); wrong['breaker'].sort()
    reject('wrong_original_branch', lambda: bind(wrong))
    reject('missing_switch_row', lambda: local_table({u:r for u,r in ROWS.items() if u != 17}))
    wrong = deepcopy(ROWS); wrong[17] = (17, wrong[17][1])
    reject('stale_switch_reply', lambda: local_table(wrong))
    wrong = deepcopy(ROWS); wrong[16] = (18,((17,26),(27,28)))
    reject('lost_local_guard', lambda: local_table(wrong))
    reject('missing_outside_mate', lambda: matching(Q+FILL[:-1], V-M-B-R, V-M-B-R))
    reject('pair_intrudes_reserved_domain', lambda: matching(Q+((0,16),), V-M-B-R))
    reject('overlapping_pair', lambda: matching(Q+(Q[0],), V-M-B-R))
    for pair in ((13,14),(31,42),(41,50)):
        bad = tuple(frozenset(p) for p in Q if p != pair)
        reject('dropped_pair_'+str(pair), lambda: coverage(edges,bad,B))
    reject('lost_reserved_guards', lambda: coverage(edges,tuple(map(frozenset,Q)),B,()))
    return names


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    need(not args.output.exists(), 'fresh report required')
    cpu, wall = time.process_time(), time.monotonic()
    def tick():
        if time.process_time()-cpu >= 8 or time.monotonic()-wall >= 25:
            raise TimeoutError('finite P52 audit cap')
    result = dict(schema='snaky-original-P52-defense-v1',status='pending',
        checker_sha256=sha(__file__),input_sha256=PINS,
        P53_resolved=False, earlier_parent_resolved=False,empty_board_result=False)
    try:
        for p,h in PINS.items():
            need(sha(BASE/p)==h,'changed input '+p)
        accepted=json.loads((BASE/'verification/browser_twentyfirst_independent05.json').read_text())
        need(accepted['status']=='verified_physical_M43_reply_reduction_and_two_frontier_inventories',
             'wrong original frontier source')
        state=next(row['state'] for row in accepted['frontiers'] if row['first_breaker_reply']==52)
        edges=literal_targets()
        result.update(defense=audit(state,edges,tick),negative_controls=controls(state,edges),
                      literal_targets=len(edges),status='verified_complete_original_P52_defense')
    except (ValueError,KeyError,TypeError,OSError,TimeoutError) as error:
        result.update(status='incomplete' if isinstance(error,TimeoutError) else 'rejected',reason=str(error))
    result.update(process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall,
                  created_utc=datetime.now(timezone.utc).isoformat())
    with args.output.open('x') as f:
        json.dump(result,f,sort_keys=True,indent=2); f.write('\n')
    print(json.dumps({k:result[k] for k in ('status','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_complete_original_P52_defense')


if __name__=='__main__':
    raise SystemExit(main())
