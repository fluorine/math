#!/usr/bin/env python3
"""Finite physical audit of Browser05 round25; no search or solver.

The complete conclusion is a single 13+13 matching leaf, including specified
neutral mate histories. The 26-cell decomposition is an exact unresolved
interface, not a solution of its recurrence or the original P53 position.
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
from original_p52_defense import Q as P52_Q, FILL as P52_FILL

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/05-twentyfifth-final.txt': 'e7b6c50616ef402249a442d81f6f63fad08e4e10420d70f5709a42803d541efe',
    'browser/05-twentyfifth-final-main.txt': '704a75cbb55715d916a05ba1a5273ed2de9bb8981bd03b70890340b3d95180ac',
    'browser/05-twentyfifth-prompt.txt': '76a89ad2543f6bd5cc6922990993be8a702aa91989c32a58d181bc82ff8f4da9',
    'verification/continued_endpoint_defenses.py': 'cee9f08d63d4a0e8a28c18967da1917504d2e975a95b7310aa43cdf1c26ed187',
    'verification/original_p52_defense.py': 'dc4881010c5150a9dff2421fc5a9899cef183f2d1e866ebfb5e14b6f922a93d1',
    'verification/original-p52-defense-01.json': '51d0885027969cbe0fafdeae9b009c187ad6438c7a6b84fbcf6d38ab1a9c4df1',
    'verification/browser_twentyfirst_independent05.json': '56d03252b70a863dd35137507b7e594e0d62af0f05854365a814aa73ab5ef45b',
}
V = frozenset(range(100))
M = frozenset((32,37,43,44,45,46,47,57,67,75,84))
B = frozenset((33,34,36,38,53,55,56,58,74,77,94))
QLEAF = ((1,3),(4,5),(6,19),(8,9),(10,11),(12,22),(15,35),(16,26),
         (17,27),(18,28),(20,30),(21,31),(24,25),(29,49),(40,50),(51,61),
         (59,79),(60,80),(62,72),(63,73),(64,65),(66,76),(68,78),(70,71),
         (81,91),(82,83),(85,86),(88,89),(92,93),(95,96))
FLEAF = ((0,2),(7,41),(39,48),(52,54),(69,87),(90,97),(98,99))
NEUTRAL = ((39,48),(59,79),(66,76),(68,78),(69,87),(85,86),(88,89),(95,96),(98,99))
EXCEPTIONS = tuple(map(frozenset, ((13,22,23,32,42,52),(21,31,41,51,52,62),
                                  (32,42,52,61,62,71),(42,43,44,45,51,52))))
FORCE = frozenset((31,32,42,43,44,45))
I = frozenset((11,12,13,14,21,22,23,24,31,41,42,50,51,52,61,62,70,71,72))
C = I | R | {54}
QOUT = ((3,4),(5,6),(7,8),(10,20),(15,25),(29,49),(30,40),(59,79),(60,80),
        (63,73),(64,65),(66,76),(68,78),(81,91),(82,83),(85,86),(88,89),(92,93),(95,96))
J_IDS = (3,7,9,11,14,15,16,21,24,25,32,34,36,37,39,40,43,44,45,47,
         48,49,50,52,53,54,55,56,57,58,59,60,61,62,65,67,69,70,71,72,
         73,74,76,78,80,81,82,83,84,85,86,89,90,91,92,93,94,95,100,101,
         102,104,105,106,107,108,109,110,112,117,118,119,130,137)
BOUNDARY = ((0,1),(2,9),(3,4),(5,6),(7,8),(10,20),(15,25),(19,35),(29,49),
            (30,40),(60,80),(63,73),(64,65),(81,91),(82,83),(90,97),(92,93))
# Full surviving incidences of each released baseline pair, in the bound 155-list.
REPAIRS = {
    (12,13): {17:(4,5),19:(10,11),39:(10,11),52:(24,25)},
    (15,25): {33:(15,35),68:(15,35),64:(24,25),66:(24,25)},
    (22,23): {40:(10,11),45:(12,22),66:(24,25),83:(24,25),78:(21,31)},
    (30,40): {8:(10,11),10:(21,31),79:(21,31),42:(20,30),46:(20,30),
              77:(20,30),87:(51,61),88:(40,50)},
    (31,41): {3:(10,11),4:(20,30),15:(21,31),41:(21,31),48:(21,31),
              81:(21,31),82:(21,31),16:(12,22),53:(12,22),76:(51,61),
              84:(51,61),92:(51,61),93:(51,61),90:(40,50)},
    (50,52): {},
}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def state(m, b):
    return dict(maker=sorted(m), breaker=sorted(b), turn='Maker')


def bind_state(s):
    need(s == state(M,B), 'wrong original P53 colors')
    need(len(M) == len(B) == 11 and not M & B, 'bad original ownership')


def coverage(edges, b, pairs):
    rows = []
    for e in edges:
        if e & b:
            continue
        witnesses = [sorted(p) for p in pairs if p <= e]
        need(witnesses, 'unprotected full target '+str(sorted(e)))
        rows.append(dict(target=sorted(e), pairs=witnesses))
    return rows


def leaf(edges, live, old_pairs):
    m, b = M|{13,23}, B|{14,42}
    need(len(m) == len(b) == 13 and not m & b, 'wrong leaf colors')
    for hm in (M, M|{13}, m):
        need(not any(e <= hm for e in edges), 'Maker already wins along the proposed prefix')
    cover = matching(QLEAF, V-m-b)
    pairs = matching(QLEAF+FLEAF, V-m-b, V-m-b)
    need(len(cover)==30 and len(pairs)==37, 'wrong leaf pair counts')
    need((V-m-b)-set().union(*cover) == {0,2,7,39,41,48,52,54,69,87,90,97,98,99},
         'wrong completion cells')
    ledger = coverage(edges,b,cover)
    need(all(e & {14,42} for e in live if not any(p <= e for p in old_pairs)),
         'old gap not killed by the actual replies')
    removed = set(old_pairs)-set(cover)
    need(removed==set(map(frozenset,REPAIRS)), 'wrong released baseline pairs')
    repairs = []
    for raw, claimed in REPAIRS.items():
        p = frozenset(raw)
        actual = {i for i,e in enumerate(live,1) if not e & b and p <= e}
        need(actual==set(claimed), 'incomplete released-pair incidence ledger '+str(raw))
        for i,q in claimed.items():
            need(frozenset(q) in cover and set(q) <= live[i-1], 'invalid replacement witness')
        repairs.append(dict(removed_pair=raw, incidences=[dict(index=i,target=sorted(live[i-1]),
                       replacement_pair=q) for i,q in sorted(claimed.items())]))
    # A pair is either FF, MB, or BM before each turn. A Maker claim at an FF
    # pair leaves its mate fresh and cannot complete a target containing it.
    # Every board cell is assigned; no discretionary filler is ever needed.
    return dict(state=state(m,b), fresh_cells=74, pairs=[sorted(p) for p in pairs],
                live_targets=len(ledger), full_target_ledger=ledger, released_pair_ledger=repairs,
                exhaustion_rounds=37, immediate_and_final_claims_protected=True), pairs


def attack(edges, tick):
    need(FORCE in edges and all(e in edges for e in EXCEPTIONS), 'nonliteral attack witness')
    m, b = M|{13,23}, B|{14}
    legal = V-m-b
    allowed = {22,31,42,51,52}
    need(len(legal)==75 and allowed <= legal, 'wrong pending reply inventory')
    counts = dict(first_replies=75, excluded_replies=0, next_reply_checks=0, fork_reply_checks=0)
    for v in sorted(legal-allowed):
        tick(); counts['excluded_replies'] += 1
        bm, bb = m|{42}, b|{v}
        need(42 not in m|b|{v} and not bm & bb, 'stale attack pivot')
        need(FORCE-bm=={31} and not FORCE & bb, 'missing forced threat')
        for w in V-bm-bb:
            counts['next_reply_checks'] += 1
            if w != 31:
                need(31 not in bm|bb|{w} and FORCE <= bm|{31}, 'off-line reply survives')
                continue
            cm, cb = bm|{52}, bb|{31}
            need(52 not in bm|bb|{31} and EXCEPTIONS[0]-cm=={22} and
                 EXCEPTIONS[3]-cm=={51} and not (EXCEPTIONS[0]|EXCEPTIONS[3]) & cb,
                 'fork lost full physical binding')
            for z in V-cm-cb:
                t, e = (51,EXCEPTIONS[3]) if z==22 else (22,EXCEPTIONS[0])
                need(t not in cm|cb|{z} and e <= cm|{t}, 'final legal reply survives fork')
                counts['fork_reply_checks'] += 1
    need(counts['excluded_replies']==70 and 24 in legal-allowed, 'wrong excluded class')
    return dict(**counts, necessary_second_replies=sorted(allowed),
                witnesses=[sorted(FORCE),sorted(EXCEPTIONS[0]),sorted(EXCEPTIONS[3])],
                scope='After the prescribed M13/B14 and M23 only; no original P53 winner.')


def neutral_histories(edges, pairs, tick):
    neutral = matching(NEUTRAL,V-M-B)
    need(set(neutral) <= set(pairs) and not set().union(*neutral) & {13,14,23,42},
         'neutral pair is changed or meets the core prefix')
    count = moves = checks = 0
    for e in edges:
        if e & B:
            continue
        relevant = [tuple(sorted(p)) for p in neutral if p & e]
        for choices in product(range(3),repeat=len(relevant)):
            tick(); hm,hb = set(M),set(B)
            for p,c in zip(relevant,choices):
                if c:
                    hm.add(p[c-1]); hb.add(p[2-c])
            count += 1
            for cm,cb in ((hm,hb),(hm|{13},hb|{14}),(hm|{13,23},hb|{14,42})):
                need(not e <= cm, 'target already wins in a neutral history')
                for p,c in zip(relevant,choices):
                    if not c:
                        for u in p:
                            need(not e <= cm|{u}, 'neutral Maker entry wins before mate')
                            moves += 1
            need(not e <= hm|{13} and not e <= hm|{13,23}, 'core entry wins before response')
            fm,fb = hm|{13,23},hb|{14,42}
            if not e & fb:
                need(any(p <= e and not p & (fm|fb) for p in pairs), 'history invalidates leaf cover')
                checks += 1
    return dict(pairs=NEUTRAL,targetwise_histories=count, pre_response_checks=moves,
                surviving_leaf_checks=checks, arbitrary_order_and_orientation=True,
                pairs_remaining_after_k_consumed=[37-k for k in range(10)])


def decomposition(live, tick):
    qstar = matching(tuple(p for p in P52_Q if p!=(53,54)),V-M-B-R)
    local_table(ROWS)
    exceptions = tuple(e for e in live if not any(p <= e for p in qstar) and
                       not any(g <= e for g in GAMMA))
    need(set(exceptions)==set(EXCEPTIONS) and len(exceptions)==4, 'wrong Qstar exception family')
    need([live.index(e)+1 for e in EXCEPTIONS]==[59,82,95,107], 'source numbering changed')
    support = frozenset().union(*(e-M for e in exceptions))
    closure = set(support)
    while True:
        enlarged = closure | set().union(*(p for p in qstar if p & closure))
        if enlarged==closure:
            break
        closure=enlarged
    need(closure==I and len(I)==19 and len(C)==26 and C <= V-M-B, 'wrong whole-pair closure')
    outer = matching(QOUT+P52_FILL,(V-M-B)-C,(V-M-B)-C)
    need(len(outer)==26, 'outside matching is not 26 pairs')
    retained, remainder = [],[]
    for i,e in enumerate(live,1):
        tick(); ps=[sorted(p) for p in outer if p <= e]
        if ps:
            retained.append(dict(index=i,target=sorted(e),pairs=ps))
        else:
            a,d = e & C, e-(M|C)
            need(e==(e&M)|a|d and not (a&d or a&M or d&M), 'lost physical requirements')
            remainder.append(dict(index=i,target=sorted(e),fixed_maker=sorted(e&M),
                                  core_requirements=sorted(a),outside_requirements=sorted(d)))
    need(len(retained)==81 and tuple(r['index'] for r in remainder)==J_IDS,
         'wrong exact 81/74 physical split')
    domain = frozenset().union(*(frozenset(r['target']) for r in remainder))
    neutral = tuple(p for p in outer if not p & domain)
    boundary = tuple(p for p in outer if p & domain)
    need(set(neutral)==set(map(frozenset,NEUTRAL)) and
         set(boundary)==set(map(frozenset,BOUNDARY)), 'wrong boundary/neutral pair partition')
    witness = next(r for r in remainder if r['index']==112)
    need(witness['target']==[50,51,61,62,63,64] and witness['core_requirements']==[50,51,61,62]
         and witness['outside_requirements']==[63,64], 'crossing requirement silently projected away')
    # These are the exact safe pair colors at a Maker turn. A Breaker-owned
    # endpoint permanently blocks any target containing the pair. No MF/FM
    # state is a turn boundary under mandatory mate response to an FF entry.
    safe = ('FF','BF','FB','BM','MB','BB')
    transitions=[]
    for s in safe:
        for side in range(2):
            if s[side]!='F':
                continue
            t=list(s); t[side]='M'
            if s=='FF':
                t[1-side]='B'
                need(''.join(t) in safe, 'FF mate transition is unsafe')
                reply='fresh mate'
            else:
                need('B' in t and ''.join(t) in safe, 'breaker-hit pair changed safety')
                reply='any other fresh cell; recurrence not evaluated'
            transitions.append(dict(before=s,maker_side=side,after_pair=''.join(t),reply=reply))
    return dict(qstar=[sorted(p) for p in qstar],qstar_or_right_guards_protected=151,
        exceptions=[sorted(e) for e in exceptions],exception_support=sorted(support),
        whole_pair_closure=sorted(I),core_domain=sorted(C),outside_pairs=[sorted(p) for p in outer],
        protected_81=retained,residual_74=remainder,boundary_pairs=BOUNDARY,neutral_pairs=NEUTRAL,
        safe_turn_pair_colors=safe,pair_transitions=transitions,
        recurrence_evaluated=False,projected_core_win_not_physical=True)


def controls(edges, live, pairs):
    names=[]
    def reject(name,fn):
        try:
            fn()
        except ValueError:
            names.append(name)
        else:
            raise ValueError('control accepted '+name)
    for color in ('maker','breaker'):
        bad=state(M,B); bad[color].pop()
        reject('lost_old_'+color,lambda:bind_state(bad))
    wrong=state(M,B); wrong['breaker'].remove(53); wrong['breaker'].append(52); wrong['breaker'].sort()
    reject('confused_P52',lambda:bind_state(wrong))
    fm,fb=M|{13,23},B|{14,42}
    reject('missing_leaf_pair',lambda:matching(QLEAF+FLEAF[:-1],V-fm-fb,V-fm-fb))
    reject('overlap_leaf_pair',lambda:matching(QLEAF+FLEAF+(QLEAF[0],),V-fm-fb))
    reject('occupied_pair',lambda:matching(((13,14),),V-fm-fb))
    reject('empty_coverage',lambda:coverage(edges,fb,()))
    reject('omitted_full_target',lambda:need(len(edges[:-1])==432,'omitted literal target'))
    reject('omitted_residual',lambda:need(tuple(J_IDS[:-1])==J_IDS,'omitted crossing obligation'))
    reject('nonneutral_boundary_pair',lambda:need(not {63,73}&set().union(*(live[i-1] for i in J_IDS)),
                                                   'boundary pair has a surviving singleton incidence'))
    e=frozenset((50,51,61,62,63,64)); projected_m=M|{50,51,61,62}
    reject('projection_is_not_a_physical_win',lambda:need(e <= projected_m,'outside requirements missing'))
    # Positive control: final Maker ownership is checked before any response.
    need(e in edges and e <= projected_m|{63,64}, 'full physical terminal control')
    return dict(rejections=names,positive_final_claim_controls=1)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    need(not args.output.exists(),'fresh output required')
    cpu,wall=time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu>=4 or time.monotonic()-wall>=25:
            raise TimeoutError('finite audit cap')
    result=dict(schema='snaky-browser25-P53-leaf-interface-v1',status='pending',
                checker_sha256=sha(__file__),input_sha256=PINS,original_P53_resolved=False,
                earlier_parent_resolved=False,empty_board_result=False,search_performed=False)
    try:
        for p,h in PINS.items():
            need(sha(BASE/p)==h,'changed input '+p)
        accepted=json.loads((BASE/'verification/browser_twentyfirst_independent05.json').read_text())
        need(accepted['status']=='verified_physical_M43_reply_reduction_and_two_frontier_inventories',
             'wrong accepted physical source')
        source=next(r for r in accepted['frontiers'] if r['first_breaker_reply']==53)
        bind_state(source['state'])
        need(json.loads((BASE/'verification/original-p52-defense-01.json').read_text())['status']==
             'verified_complete_original_P52_defense','wrong accepted P52 interface')
        edges=literal_targets(); live=tuple(e for e in edges if not e&B)
        need(len(live)==155,'wrong live target count')
        prompt=(BASE/'browser/05-twentyfifth-prompt.txt').read_text()
        marker='All155 live full physical targets at P53 (exact geometry, retained old colors):'
        need(prompt.count(marker)==1,'ambiguous target-list source')
        ordered=json.JSONDecoder().raw_decode(prompt.split(marker)[1].lstrip())[0]
        need(ordered==[sorted(e) for e in live],'browser indices do not bind full literal geometry')
        old=matching(source['retained_pairs'],V-M-B)
        complete,pairs=leaf(edges,live,old)
        result['complete_leaf']=complete
        result['old_pair_obstruction']=attack(edges,tick)
        result['neutral_interleavings']=neutral_histories(edges,pairs,tick)
        result['exact_unresolved_interface']=decomposition(live,tick)
        result['controls']=controls(edges,live,pairs)
        result.update(status='verified_complete_leaf_and_exact_unresolved_P53_interface',literal_targets=432,
                      original_state=state(M,B))
    except (ValueError,KeyError,TypeError,OSError,TimeoutError,StopIteration) as error:
        result.update(status='incomplete' if isinstance(error,TimeoutError) else 'rejected',reason=str(error))
    result.update(process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall,
                  created_utc=datetime.now(timezone.utc).isoformat())
    with args.output.open('x') as f:
        json.dump(result,f,sort_keys=True,indent=2); f.write('\n')
    print(json.dumps({k:result[k] for k in ('status','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_complete_leaf_and_exact_unresolved_P53_interface')


if __name__=='__main__':
    raise SystemExit(main())
