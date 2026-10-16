#!/usr/bin/env python3
"""Independent literal audit of the two proposed full endpoint defenses.

No constructor, browser checker or search helper is imported. The outside
matching is total; it has no discretionary fillers before the six-cell switch.
Target-wise histories enumerate all relevant outside-pair orientations. Pairs
disjoint from the target cannot affect its completion or the reserved switch.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
from itertools import product
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/05-twentythird-final.txt': '533b089f64e772a2fa9d0c823705ee68bd09cab195e94369af49a7fd4aa84379',
    'verification/browser_twentysecond_independent05.json': 'eb516db865d288b8cef9f58a9bf25bbb1f736340c3ee295ca2dbd128e7b43678',
}
R = frozenset((16, 17, 18, 26, 27, 28))
GAMMA = tuple(map(frozenset, ((16,17), (16,26,27), (17,18,27), (18,27,28))))
COMMON = ((1,3),(4,5),(6,19),(7,8),(13,14),(15,25),(21,23),
          (29,49),(30,40),(59,79),(60,80),(62,72),(64,65),(81,91),
          (82,83),(85,86),(88,89),(92,93),(95,96))
EXTRA = {52: ((41,50),(51,61),(70,71)), 53: ((63,73),)}
FILL = {
    52: ((0,2),(9,10),(11,20),(24,35),(39,48),(69,87),(90,97),(98,99)),
    53: ((0,2),(9,10),(11,20),(24,35),(39,48),(54,69),(70,87),(90,97),(98,99)),
}
ROWS = {
    16: (17, ((26,27),(18,28))),
    17: (16, ((18,27),(26,28))),
    18: (27, ((16,17),(26,28))),
    26: (27, ((16,17),(18,28))),
    27: (17, ((16,26),(18,28))),
    28: (27, ((16,17),(18,26))),
}
STATES = {
    52: ({22,32,37,42,43,44,45,46,47,53,57,63,67,75,76,78,84},
         {12,31,33,34,36,38,52,54,55,56,58,66,68,73,74,77,94}),
    53: ({22,32,37,41,42,43,44,45,46,47,51,57,61,67,75,76,78,84},
         {12,31,33,34,36,38,50,52,53,55,56,58,66,68,71,74,77,94}),
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def literal_targets():
    shape = ((0,0),(1,0),(2,0),(3,0),(3,1),(4,1))
    orientations = set()
    for flip in (-1, 1):
        for turns in range(4):
            points = []
            for x, y in shape:
                x *= flip
                for _ in range(turns):
                    x, y = -y, x
                points.append((x, y))
            xmin, ymin = min(x for x,y in points), min(y for x,y in points)
            orientations.add(tuple(sorted((x-xmin,y-ymin) for x,y in points)))
    need(len(orientations) == 8, 'wrong D4 orbit')
    edges = set()
    for shape in orientations:
        for dx in range(10-max(x for x,y in shape)):
            for dy in range(10-max(y for x,y in shape)):
                edges.add(frozenset(10*(dy+y)+dx+x for x,y in shape))
    need(len(edges) == 432 and all(len(e) == 6 for e in edges), 'wrong literal geometry')
    return tuple(sorted(edges, key=lambda e: tuple(sorted(e))))


def matching(raw, available, expected_cells=None):
    pairs, used = [], set()
    for row in raw:
        need(len(row) == 2 and all(type(x) is int for x in row), 'malformed pair')
        pair = frozenset(row)
        need(len(pair) == 2 and pair <= available and not pair & used, 'pair is occupied or overlaps')
        used.update(pair)
        pairs.append(pair)
    if expected_cells is not None:
        need(used == set(expected_cells), 'matching is not total on its declared domain')
    return tuple(pairs)


def local_table(rows):
    need(set(rows) == R, 'missing switch entry')
    for u, (v, raw) in rows.items():
        need(v in R-{u}, 'switch reply is not fresh')
        pairs = matching(raw, R-{u,v}, R-{u,v})
        for g in GAMMA:
            need(len(g) >= 2 and (v in g or any(p <= g-{u} for p in pairs)), 'unprotected local guard')


def check_state(key, endpoint, edges, rows, common, guard):
    m, b = map(frozenset, STATES[key])
    need(endpoint == dict(board=[0,0,9,9], turn='Maker', maker=sorted(m), breaker=sorted(b)),
         'accepted endpoint loses old physical ownership')
    free = frozenset(range(100))-m-b
    need(not m & b and R <= free and len(free) == (66 if key == 52 else 64), 'invalid endpoint')
    cover = matching(common+EXTRA[key], free-R)
    outer = matching(common+EXTRA[key]+FILL[key], free-R, free-R)
    live = tuple(e for e in edges if not e & b)
    ledger = []
    for e in live:
        guard()
        need(not e <= m, 'already completed physical target')
        ps, gs = [sorted(p) for p in cover if p <= e], [sorted(g) for g in GAMMA if g <= e]
        need(ps or gs, 'uncovered full physical target: '+str(sorted(e)))
        ledger.append(dict(target=sorted(e), outside_pairs=ps, switch_guards=gs))
    # Every first move is legal and nonwinning before the actual response.
    for u in free:
        guard()
        need(not any(e <= m|{u} for e in live), 'immediate first-entry win')
        if u not in R:
            p = next(p for p in outer if u in p)
            need(len(p-{u}) == 1 and p-{u} <= free-{u}, 'missing fresh outside mate')
    commitments = []
    for u, (v, raw) in rows.items():
        local = matching(raw, R-{u,v}, R-{u,v})
        pairs = matching(tuple(tuple(p) for p in outer+local), free-{u,v}, free-{u,v})
        surviving = [e for e in live if v not in e]
        need(all(any(p <= e for p in pairs) for e in surviving), 'incomplete full-board commitment')
        commitments.append(dict(maker=u, reply=v, pairs=[sorted(p) for p in pairs], live_targets=len(surviving)))
    # A relevant outside pair is untouched or consumed in either orientation.
    # Other completed pairs are disjoint from e and R and cannot alter this check.
    histories, switch_checks, blocked = 0, 0, 0
    history_hash = hashlib.sha256()
    for e in live:
        relevant = [tuple(sorted(p)) for p in outer if p & e]
        for choices in product(range(3), repeat=len(relevant)):
            guard(); hm, hb = set(m), set(b)
            for pair, choice in zip(relevant, choices):
                if choice:
                    hm.add(pair[choice-1]); hb.add(pair[2-choice])
            need(m <= hm and b <= hb and not hm & hb and not R & (hm|hb), 'history reset or intrusion')
            histories += 1
            history_hash.update(bytes(sorted(e))+bytes(choices))
            if e & hb:
                blocked += 1
                continue
            need(not e <= hm, 'outside waiting already wins')
            for u, (v, raw) in rows.items():
                need(not e <= hm|{u}, 'switch entry wins before response')
                if v not in e:
                    available = frozenset(range(100))-hm-hb-{u,v}
                    witnesses = outer+tuple(map(frozenset, raw))
                    need(any(p <= e and p <= available for p in witnesses), 'history invalidates committed protector')
                switch_checks += 1
    # Before R entry, 2r+6 fresh cells remain; after it, 2r+4 remain.
    # At every later Maker turn a total matching supplies a fresh physical mate.
    exhaustion = [dict(outside_pairs_left=r, before_switch_free=2*r+6,
                       after_switch_free=2*r+4) for r in range(len(outer)+1)]
    return dict(state=endpoint, free_cells=len(free), live_targets=len(live),
                covering_pairs=[sorted(p) for p in cover], outside_perfect_matching=[sorted(p) for p in outer],
                coverage_ledger=ledger, commitments=commitments, all_first_entries_checked=len(free),
                targetwise_histories=histories, already_blocked_histories=blocked,
                live_history_switch_checks=switch_checks, history_records_sha256=history_hash.hexdigest(),
                exhaustion_cases=exhaustion, full_conditional_physical_defense=True)


def controls(report, edges, guard):
    result = []
    def reject(name, action):
        try:
            action()
        except ValueError:
            result.append(name)
            return
        raise ValueError('negative control accepted: '+name)
    reject('missing_switch_entry', lambda: local_table({u:r for u,r in ROWS.items() if u != 17}))
    bad = deepcopy(ROWS); bad[17] = (17, bad[17][1])
    reject('owned_switch_reply', lambda: local_table(bad))
    overlap = deepcopy(ROWS); overlap[16] = (17, ((26,27),(26,28)))
    reject('overlapping_local_pairs', lambda: local_table(overlap))
    wrong = deepcopy(ROWS); wrong[16] = (18, ((17,26),(27,28)))
    reject('unprotected_switch_guard', lambda: local_table(wrong))
    reject('outside_pair_touches_core', lambda: matching(((1,16),), frozenset(range(100))-R))
    reject('missing_outside_mate', lambda: matching(((1,3),), {1,3,5,7}, {1,3,5,7}))
    endpoint = deepcopy(report['forced_prefixes']['52']['final_state']); endpoint['maker'].remove(84)
    reject('forgotten_old_Maker', lambda: check_state(52, endpoint, edges, ROWS, COMMON, guard))
    endpoint = deepcopy(report['forced_prefixes']['52']['final_state']); endpoint['breaker'].remove(94)
    reject('forgotten_old_Breaker', lambda: check_state(52, endpoint, edges, ROWS, COMMON, guard))
    # Missing physical protection is detected directly, not by its expected count.
    p = matching(tuple(x for x in COMMON if x != (13,14))+EXTRA[52], frozenset(range(100))-R)
    witness = frozenset((2,3,13,14,15,16))
    reject('lost_crossing_target', lambda: need(any(q <= witness for q in p+GAMMA), 'uncovered crossing target'))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    need(not args.output.exists(), 'fresh report path required')
    cpu, wall = time.process_time(), time.monotonic()
    def guard():
        if time.process_time()-cpu > 12 or time.monotonic()-wall > 45:
            raise TimeoutError('finite endpoint audit limit')
    out = dict(schema='snaky-continued-endpoint-defense-v1', status='pending',
               checker_sha256=sha(__file__), input_sha256=PINS,
               original_11plus11_frontiers_resolved=False, empty_board_result=False)
    try:
        for name, h in PINS.items():
            need(sha(BASE/name) == h, 'changed input '+name)
        source = json.loads((BASE/'verification/browser_twentysecond_independent05.json').read_text())
        need(source['status'] == 'verified_static_matching_obstructions_and_physical_forcing_prefixes', 'unaccepted endpoint source')
        edges = literal_targets(); local_table(ROWS)
        out['endpoints'] = {str(k):check_state(k, source['forced_prefixes'][str(k)]['final_state'],
                                             edges, ROWS, COMMON, guard) for k in STATES}
        out.update(literal_targets=432, literal_targets_sha256=canonical([sorted(e) for e in edges]),
                   local_guards=[sorted(g) for g in GAMMA],
                   negative_controls=controls(source, edges, guard),
                   status='verified_two_complete_conditional_physical_defenses')
    except (ValueError, KeyError, TypeError, OSError, TimeoutError) as error:
        out.update(status='incomplete' if isinstance(error, TimeoutError) else 'rejected', reason=str(error))
    out.update(process_cpu_seconds=time.process_time()-cpu, elapsed_seconds=time.monotonic()-wall,
               created_utc=datetime.now(timezone.utc).isoformat())
    with args.output.open('x') as stream:
        json.dump(out, stream, indent=2, sort_keys=True); stream.write('\n')
    print(json.dumps({k:out[k] for k in ('status','process_cpu_seconds','elapsed_seconds')}))
    return int(out['status'] != 'verified_two_complete_conditional_physical_defenses')


if __name__ == '__main__':
    raise SystemExit(main())
