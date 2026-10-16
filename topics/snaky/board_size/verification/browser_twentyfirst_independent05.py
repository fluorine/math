#!/usr/bin/env python3
"""Literal physical M43 reply classification and two full S9 frontiers.

No constructor, search, solver, or projected-game helper is imported. Every
legal physical reply to the displayed forcing tree is enumerated; the two
surviving11+11 states retain every old color. The29-pair inventories are
diagnostics, not complete defenses.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(BASE/'breaker'))
from check_pairing import check, winning_sets

M0 = frozenset((37,44,45,46,47,57,67,75,84))
B0 = frozenset((34,36,38,55,56,58,74,77,94))
BOARD = frozenset(range(100))
ACCEPTED = 'verification/upstream11-physical-matching-result-01.json'
CERTIFICATE = 'verification/upstream11-physical-matching-result-01.pairing.json'
FRONTIER = 'verification/upstream11-seed-frontier-01.json'
PINS = {
    'browser/05-twentyfirst-final-section.txt': 'b634e970c955ddf7171db6d8cbfb04d8d4b0593e95e163f6ab6a513062e87cf7',
    ACCEPTED: '6ec266d1c68e26e96f4ca292e8177d1ebb5494f9599089e944e5ad5168c08cb0',
    CERTIFICATE: 'dd3a93b074a5c1f2ed6247979fead37ea9ae01b5ad8b7fc0d09a4ec93fab44b9',
    FRONTIER: '9eb1cbca1e5bc832ad9156397d08687412429ff5d435ff1218101bf8adb07753',
    'verification/check_upstream11_physical_matching.py': '55d8aa997fc9360c2b41697061a0663505518b7342afd027b3c5cce935fbaf60',
    'breaker/check_pairing.py': 'f24d5a389197f5010afc88036e0b849c3f31caadb60c142f29c1b3c684191056',
}
W = {name:frozenset(cells) for name,cells in {
    'H':(44,45,46,47,53,54),
    'C1':(41,42,43,44,50,51),
    'C2':(42,43,44,45,51,52),
    'C3':(32,33,43,44,45,46),
    'C4':(43,44,45,46,52,53),
    'A1':(2,3,13,14,15,16), 'A2':(6,7,13,14,15,16),
    'A3':(3,4,14,15,16,17), 'A4':(7,8,14,15,16,17),
    'A5':(14,15,16,17,23,24), 'A6':(13,14,24,25,26,27),
    'A7':(5,6,7,8,14,15),
    'D1':(1,11,12,22,32,42), 'D2':(12,22,32,41,42,51),
    'D3':(11,21,22,32,42,52), 'D4':(21,31,32,42,52,62),
    'D5':(32,42,52,61,62,71), 'D6':(1,11,21,31,32,42),
    'D7':(31,32,42,43,44,45), 'D8':(12,22,32,42,43,53),
}.items()}
EXPECTED_GAPS = {
    52:tuple(f'A{i}' for i in range(1,8))+('C1','D1','D2','D6','D7','D8'),
    53:tuple(f'A{i}' for i in range(1,8))+('C1','C2')+tuple(f'D{i}' for i in range(1,8)),
}


def need(ok,message):
    if not ok:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def fresh(q,maker,breaker):
    need(type(q) is int and q in BOARD-maker-breaker,'claim is not a fresh physical cell')
    return maker | {q}


def replies(maker,breaker):
    return tuple(sorted(BOARD-maker-breaker))


def check_reply_domain(actual,maker,breaker):
    need(tuple(actual) == replies(maker,breaker),'physical reply domain omitted, reordered, or repeated a cell')


def terminal(maker,breaker,target,edges):
    need(not maker & breaker and target in edges and target <= maker and not target & breaker,
         'terminal does not own an unblocked full physical Snaky')


def source(accepted,certificate,frontier,edges):
    old_m,old_b = M0 | {11,21},B0 | {14,43}
    need(accepted['status'] == 'verified_conditional_upstream11_full_physical_pairing'
         and accepted['checker_sha256'] == PINS['verification/check_upstream11_physical_matching.py']
         and accepted['certificate'] == certificate and certificate['schema'] == 'snaky-static-pairing-v1'
         and certificate['size'] == 10 and certificate['maker'] == sorted(old_m)
         and certificate['breaker'] == sorted(old_b), 'accepted pairing or complete source colors differ')
    checked = check(10,certificate['pairs'],old_m,old_b)
    need(checked['pairs'] == 32 and checked['live_placements'] == 144,'accepted S11 pairing differs')
    pairs = tuple(map(frozenset,certificate['pairs']))
    need(all(p <= BOARD-M0-B0 for p in pairs),'old matching is not fresh at S9')
    initial = [e for e in edges if not e & B0 and not any(p <= e for p in pairs)]
    need(len(M0) == len(B0) == 9 and len(BOARD-M0-B0) == 82
         and not any(e <= M0 for e in edges),'invalid physical S9 root')
    need(frontier['status'] == 'finite_frontier_calculation_only'
         and frontier['source_sha256'] == PINS[CERTIFICATE]
         and frontier['initial_state'] == dict(maker=sorted(M0),breaker=sorted(B0))
         and frontier['pair_count'] == 32 and frontier['live_count'] == 194
         and frontier['covered_count'] == 176 and frontier['uncovered_count'] == len(initial) == 18
         and {frozenset(r['full']) for r in frontier['uncovered_targets']} == set(initial),
         'accepted18-gap initial inventory differs from literal full geometry')
    return pairs,initial


def bind_frontier(reply,maker,breaker):
    need(reply in (52,53) and maker == M0 | {43,32} and breaker == B0 | {reply,33}
         and len(maker) == len(breaker) == 11 and not maker & breaker,
         'frontier loses old colors or adds an unplayed claim')
    return dict(maker=sorted(maker),breaker=sorted(breaker),turn='Maker')


def inventory(reply,pairs,edges):
    maker,breaker = M0 | {43,32},B0 | {reply,33}
    state = bind_frontier(reply,maker,breaker)
    free = BOARD-maker-breaker
    retained = tuple(p for p in pairs if p <= free)
    removed = tuple(p for p in pairs if p not in retained)
    expected_removed = {frozenset((24,33)),frozenset((32,42)),
                        frozenset((50,52) if reply == 52 else (53,54))}
    need(len(retained) == 29 and set(removed) == expected_removed
         and len(set().union(*retained)) == 58,'retained29-pair freshness or disjointness differs')
    rows = []
    for edge in sorted(edges,key=lambda e:sorted(e)):
        hits = [sorted(p) for p in retained if p <= edge]
        rows.append(dict(target=sorted(edge),breaker_hits=sorted(edge & breaker),
            maker_owned=sorted(edge & maker),required_free=sorted(edge & free),covering_pairs=hits))
    live = [r for r in rows if not r['breaker_hits']]
    uncovered = [r for r in live if not r['covering_pairs']]
    expected = {W[label] for label in EXPECTED_GAPS[reply]}
    need(not any(e <= maker for e in edges) and len(free) == 78
         and {frozenset(r['target']) for r in uncovered} == expected
         and len(uncovered) == (13 if reply == 52 else 16), 'claimed exact full-target defect inventory differs')
    return dict(first_breaker_reply=reply,actual_prefix=[dict(maker=43,breaker=reply),dict(maker=32,breaker=33)],
        state=state,state_sha256=hashlib.sha256(canonical(state)).hexdigest(),free_cells=sorted(free),
        retained_pairs=[sorted(p) for p in retained],removed_pairs=[sorted(p) for p in removed],
        physical_targets=rows,live_target_count=len(live),covered_live_targets=len(live)-len(uncovered),
        uncovered_live_targets=uncovered,uncovered_count=len(uncovered),expected_gap_labels=EXPECTED_GAPS[reply],
        complete_static_matching=False,full_game_result=None)


def controls(accepted,certificate,frontier,edges):
    checks = []
    def reject(name,operation):
        try: operation()
        except ValueError as error: checks.append(dict(name=name,rejected=True,reason=str(error)))
        else: raise ValueError('negative control accepted: '+name)
    wrong = deepcopy(certificate); wrong['breaker'].remove(55)
    reject('missing_old_breaker_color',lambda:source(accepted,wrong,frontier,edges))
    m,b = M0 | {43},B0
    reject('omitted_exterior_reply',lambda:check_reply_domain(replies(m,b)[:-1],m,b))
    reject('M53_after_B53',lambda:fresh(53,m,b | {53}))
    target = W['C4']; won = M0 | {43,53,52}
    reject('blocked_terminal_target',lambda:terminal(won,B0 | {52},target,edges))
    reject('missing_owned_body_cell',lambda:terminal(won-{44},B0,target,edges))
    reject('wrong_second_breaker_claim',lambda:bind_frontier(52,M0 | {43,32},B0 | {52,31}))
    reject('projected_five_cell_target',lambda:terminal(won,B0,target-{44},edges))
    terminal(won,B0,target,edges)
    checks.append(dict(name='final_Maker_claim_checked_before_any_reply',passed=True))
    return checks


def audit(tick):
    for name,expected in PINS.items():
        tick(); need(sha(BASE/name) == expected,'changed input: '+name)
    edges = winning_sets(10)
    geometry = sorted(sorted(e) for e in edges)
    need(len(edges) == 432 and all(e in edges for e in W.values()),'literal geometry or named witness differs')
    accepted = json.loads((BASE/ACCEPTED).read_text())
    certificate = json.loads((BASE/CERTIFICATE).read_text())
    old_frontier = json.loads((BASE/FRONTIER).read_text())
    pairs,initial = source(accepted,certificate,old_frontier,edges)
    @lru_cache(maxsize=None)
    def wins(maker): return any(e <= maker for e in edges)
    counts = Counter(); terminal_counts = Counter(); terminals = hashlib.sha256(); rows = []
    minimum_free_after_win = 100
    def safe_claim(q,maker,breaker):
        after = fresh(q,maker,breaker)
        need(not wins(after),'displayed prefix should terminate at an earlier physical win')
        return after
    def record_win(q,maker,breaker,label,path):
        nonlocal minimum_free_after_win
        after = fresh(q,maker,breaker)
        terminal(after,breaker,W[label],edges)
        terminal_counts[label] += 1
        minimum_free_after_win = min(minimum_free_after_win,len(BOARD-after-breaker))
        terminals.update(canonical(dict(prefix=path,final_maker=q,target=sorted(W[label])))+b'\n')
    def fork(maker,breaker,ends,labels,path):
        need(len(set(ends)) == 2 and all(q in BOARD-maker-breaker for q in ends), 'fork endpoints not distinct and fresh')
        for q,label in zip(ends,labels):
            need(W[label]-maker == {q} and not W[label] & breaker,'fork is not a full physical one-claim threat')
        domain = replies(maker,breaker); check_reply_domain(domain,maker,breaker)
        for response in domain:
            tick(); counts['fork_breaker_replies'] += 1
            slot = 1 if response == ends[0] else 0
            record_win(ends[slot],maker,breaker | {response},labels[slot],path+[dict(breaker=response)])
        return len(domain)
    maker1 = safe_claim(43,M0,B0)
    domain1 = replies(maker1,B0); need(len(domain1) == 81,'wrong first-reply domain')
    check_reply_domain(domain1,maker1,B0)
    for first in domain1:
        tick(); breaker1 = B0 | {first}; path = [dict(maker=43,breaker=first)]
        row = dict(first_breaker_reply=first,physical_state_after_first=dict(maker=sorted(maker1),breaker=sorted(breaker1)))
        if first not in (52,53,54):
            maker2 = safe_claim(53,maker1,breaker1)
            row.update(status='physical_Maker_win',maximum_Maker_claims_from_S9=3,
                terminal_reply_branches=fork(maker2,breaker1,(52,54),('C4','H'),path+[dict(maker=53)]))
            counts['first_replies_losing_by_M53'] += 1
        else:
            maker2 = safe_claim(32,maker1,breaker1)
            domain2 = replies(maker2,breaker1); need(len(domain2) == 79 and 33 in domain2,'wrong B33 forcing domain')
            for second in domain2:
                tick(); counts['second_breaker_replies'] += 1
                if second != 33:
                    record_win(33,maker2,breaker1 | {second},'C3',path+[dict(maker=32,breaker=second)])
            breaker2 = breaker1 | {33}; path2 = path+[dict(maker=32,breaker=33)]
            if first in (52,53):
                row.update(status='unresolved_exact_frontier',forced_second_reply=33,
                    rejected_second_replies=78,frontier=bind_frontier(first,maker2,breaker2),actual_prefix=path2)
            else:
                maker3 = safe_claim(42,maker2,breaker2)
                domain3 = replies(maker3,breaker2); need(len(domain3) == 77 and 31 in domain3,'wrong B31 forcing domain')
                for third in domain3:
                    tick(); counts['third_breaker_replies'] += 1
                    if third != 31:
                        record_win(31,maker3,breaker2 | {third},'D7',path2+[dict(maker=42,breaker=third)])
                breaker3 = breaker2 | {31}; path3 = path2+[dict(maker=42,breaker=31)]
                maker4 = safe_claim(52,maker3,breaker3)
                leaves = fork(maker4,breaker3,(51,53),('C2','C4'),path3+[dict(maker=52)])
                need(leaves == 75,'wrong final fork reply domain')
                row.update(status='physical_Maker_win',maximum_Maker_claims_from_S9=5,
                    terminal_reply_branches=78+76+leaves,forced_prefix=path3)
                counts['first_replies_losing_on_B54_branch'] += 1
        rows.append(row)
    need(len(rows) == 81 and counts['first_replies_losing_by_M53'] == 78
         and counts['first_replies_losing_on_B54_branch'] == 1
         and [r['first_breaker_reply'] for r in rows if r['status']=='unresolved_exact_frontier'] == [52,53],
         'reply partition differs')
    inventories = [inventory(reply,pairs,edges) for reply in (52,53)]
    controls_result = controls(accepted,certificate,old_frontier,edges)
    need(sum(terminal_counts.values()) == 6547 and minimum_free_after_win == 73,'all-reply terminal count differs')
    return dict(status='verified_physical_M43_reply_reduction_and_two_frontier_inventories',
        original_state=dict(maker=sorted(M0),breaker=sorted(B0),turn='Maker'),
        literal_target_count=432,geometry_sha256=hashlib.sha256(canonical(geometry)).hexdigest(),
        initial_live_targets=194,accepted_initial_matching_count=32,initial_uncovered_targets=[sorted(e) for e in sorted(initial,key=lambda e:sorted(e))],
        first_reply_count=81,excluded_first_replies=79,surviving_first_replies=[52,53],
        first_reply_rows=rows,enumeration_counts=dict(counts),terminal_counts=dict(terminal_counts),
        complete_terminal_branches=sum(terminal_counts.values()),terminal_record_sha256=terminals.hexdigest(),
        minimum_free_cells_after_terminal=minimum_free_after_win,terminal_semantics='The full physical target is checked immediately after the final Maker claim, before any reply.',
        named_full_witnesses={name:sorted(target) for name,target in W.items()},frontiers=inventories,
        focused_controls=controls_result,full_S9_result=None,empty10_result=False,
        scope='Conditional physical M43 reply classification and exact two11+11 frontiers. No defense is claimed at either survivor; retained29-pair inventories are incomplete.',
        not_audited=['General outer-pair interleaving dispatcher','All neutral/unpaired-entry classifications','Further mandatory static-pair changes from browser Section7'])


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--output',type=Path,required=True)
    args = p.parse_args(argv); need(not args.output.exists(),'fresh result required')
    cpu,wall = time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu >= 4 or time.monotonic()-wall >= 25:
            raise TimeoutError('finite audit CPU/wall cap')
    try: result = audit(tick)
    except TimeoutError as error: result = dict(status='incomplete',reason=str(error),full_S9_result=None)
    except (ValueError,KeyError,TypeError,IndexError,OSError) as error:
        result = dict(status='rejected',reason=f'{type(error).__name__}: {error}',full_S9_result=None)
    result.update(checker_sha256=sha(Path(__file__)),input_sha256=PINS,
        created_utc=datetime.now(timezone.utc).isoformat(),process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x') as stream: json.dump(result,stream,indent=2,sort_keys=True); stream.write('\n')
    print(json.dumps({key:result.get(key) for key in ('status','reason','first_reply_count','excluded_first_replies','surviving_first_replies','complete_terminal_branches','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status'] in ('rejected','incomplete'))


if __name__ == '__main__':
    raise SystemExit(main())
