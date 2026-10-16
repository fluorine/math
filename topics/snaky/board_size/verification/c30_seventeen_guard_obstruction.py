#!/usr/bin/env python3
"""Independently replay Browser04's17-guard C30 attack on the full S9 board.

The literal table is input, never a searched strategy. Every fresh physical
Breaker reply is replayed with all old colors retained. Selected completions
and full physical Snaky wins are recorded separately. No S9 winner is inferred.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

from controller18_u30_obstruction import geometry, legal_responses

BASE = Path(__file__).resolve().parents[1]
ACCEPTED = 'verification/browser-twentyfourth-partition04-02.json'
CERTIFICATE = 'verification/browser-twentyfourth-partition04-02.certificate.json'
PINS = {
    ACCEPTED: '85f8f26a67056b046103ac8d79d940c065ff4d11b9348b68a4e227fbb7fa9c5e',
    CERTIFICATE: '421c4794536aa5a4306c316f17b0c2c4a076da3503b49fe7451aacc630492cf1',
    'verification/browser_twentyfourth_partition04_v2.py': '6ecb1daa2a7eeb7242884a6e3d579b17f8aad676299aac0b0bdebe4e0b06734e',
    'verification/controller18_u30_obstruction.py': 'f8e451d0de3594ee5ccb6b7a7c0ce903bffaabe5e66de201d49013f123b846e4',
    'browser/04-twentyfifth-final.txt': '8984cfbf3811796dd014a8af71d98246f4a70c880c5f9ab3949f2a1b35be8bd8',
    'browser/04-twentyfifth-final-main.txt': '69a3e5d0bcea824bdce669a39a1d45f3ba2231de90e28b0a668c0d445e22ac89',
    'browser/04-twentyfifth-prompt.txt': '79cdc91019bbabc0a624dcb8efe39d4439df890da7738eebd7ed3bd70f091031',
}
BOARD = frozenset(range(100))
M0 = frozenset((37,44,45,46,47,57,67,75,84))
B0 = frozenset((34,36,38,55,56,58,74,77,94))
C30 = frozenset((10,11,12,13,14,15,21,22,23,24,25,30,31,32,33,
    35,40,41,42,43,50,51,52,53,54,61,62,63,72,73))
GUARDS = {label:frozenset(cells) for label,cells in (
    ('C1',(53,54)), ('C2',(43,52,53)), ('C3',(32,33,43)),
    ('C4',(31,32,42,43)), ('C5',(42,43,51,52)),
    ('p',(51,61)), ('a',(10,30,31,41)), ('b',(10,11,30,40)),
    ('c',(21,30,31,40,50)), ('d',(30,40,50,61)), ('e',(31,40,41,50)),
    ('f',(11,21,30,31,40)), ('g',(11,12,21,31,41)),
    ('h',(21,31,41,50,51)), ('i',(12,22,31,32,41)),
    ('j',(14,15)), ('k',(11,12,13,14)))}
SUPPORT = frozenset().union(*GUARDS.values())
WITNESSES = {label:frozenset(cells) for label,cells in (
    ('C1',(44,45,46,47,53,54)), ('C2',(43,44,45,46,52,53)),
    ('C3',(32,33,43,44,45,46)), ('C4',(31,32,42,43,44,45)),
    ('C5',(42,43,44,45,51,52)),
    ('p',(51,61,71,80,81,90)), ('a',(0,10,20,30,31,41)),
    ('b',(1,10,11,20,30,40)), ('c',(21,30,31,40,50,60)),
    ('d',(30,40,50,60,61,71)), ('e',(31,40,41,50,60,70)),
    ('f',(1,11,21,30,31,40)), ('g',(2,11,12,21,31,41)),
    ('h',(21,31,41,50,51,60)), ('i',(2,12,22,31,32,41)),
    ('j',(5,6,7,8,14,15)), ('k',(0,1,11,12,13,14)))}
OMITTED = {label:frozenset(cells) for label,cells in (
    ('p',(71,80,81,90)), ('a',(0,20)), ('b',(1,20)), ('c',(60,)),
    ('d',(60,71)), ('e',(60,70)), ('f',(1,)), ('g',(2,)),
    ('h',(60,)), ('i',(2,)), ('j',(5,6,7,8)), ('k',(0,1)))}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def canonical(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def ordered(family):
    return sorted([sorted(t) for t in family])


def fork(maker, target1, completion1, target2, completion2):
    return dict(kind='fork', maker=maker,
        threats=[dict(target=target1,completion=completion1),
                 dict(target=target2,completion=completion2)])


def chain(steps, tail):
    for maker,reply,target in reversed(steps):
        tail = dict(kind='force',maker=maker,reply=reply,target=target,next=tail)
    return tail


def dispatch(maker, cases, otherwise):
    return dict(kind='dispatch', maker=maker,
        cases=[dict(replies=list(replies),next=child) for replies,child in cases],
        otherwise=otherwise)


def proposed_table():
    """Literal transcription; independently replayed below, with no game search."""
    beta41 = dispatch(40, [((10,11,21),fork(61,'d',50,'p',51))],
                      fork(11,'b',10,'f',21))
    beta10 = chain([(51,61,'p')], dispatch(21, [
        ((40,),chain([(41,50,'h')],fork(12,'g',11,'i',22))),
        ((50,),chain([(11,40,'f'),(12,41,'g')],fork(14,'k',13,'j',15))),
        ((11,),fork(50,'c',40,'h',41))], fork(40,'f',11,'c',50)))
    after30 = dispatch(30, [
        ((10,),beta10), ((41,),beta41),
        ((21,),chain([(10,41,'a'),(61,51,'p')],fork(40,'b',11,'d',50))),
        ((40,),chain([(51,61,'p'),(41,10,'a'),(21,50,'h')],fork(12,'g',11,'i',22))),
        ((51,),chain([(10,41,'a'),(40,11,'b')],fork(50,'c',21,'d',61))),
        ((61,),chain([(41,10,'a'),(12,22,'i'),(50,40,'e')],fork(21,'g',11,'h',51))),
        ((50,),chain([(41,10,'a'),(12,22,'i'),(14,15,'j')],fork(11,'g',21,'k',13)))],
        chain([(51,61,'p'),(41,10,'a')],fork(50,'e',40,'h',21)))
    return dispatch(43, [
        ((52,),chain([(32,33,'C3'),(31,42,'C4')],after30)),
        ((53,),chain([(32,33,'C3'),(42,31,'C4')],fork(51,'C5',52,'p',61))),
        ((54,),chain([(52,53,'C2'),(32,33,'C3')],fork(42,'C4',31,'C5',51)))],
        fork(53,'C2',52,'C1',54))


def replay(table, family, board, initial_maker, initial_breaker, edges, tick, max_claims=10):
    """Check every physical response; neither merge outside cells nor search moves."""
    board,m0,b0 = map(frozenset,(board,initial_maker,initial_breaker))
    need(not m0&b0 and m0|b0 <= board and family and
         all(t and t <= board for t in family.values()), 'invalid full initial colors/targets')
    need(not any(t <= m0 for t in family.values()) and not any(e <= m0 for e in edges),
         'game already ended before the proposed first move')
    rows, counts, leaves_by_target = [], Counter(), Counter()
    physical_edges = tuple(sorted(edges,key=lambda e:tuple(sorted(e))))

    def terminal(maker,breaker,claims):
        selected = [name for name,t in family.items() if t <= maker]
        physical = [i for i,e in enumerate(physical_edges) if e <= maker]
        need(not physical or selected, 'table would continue after an unclassified physical win')
        if not selected:
            return None
        counts['winning_leaves'] += 1
        counts['physical_winning_leaves'] += bool(physical)
        counts['selected_only_leaves'] += not physical
        counts['final_available_claim_wins'] += maker|breaker == board
        counts['maximum_maker_claims'] = max(counts['maximum_maker_claims'],claims)
        leaves_by_target.update(selected)
        return dict(selected_wins=selected, physical_target_indices=physical,
                    board_exhausted=maker|breaker == board, stop_before_reply=True)

    def complete(cell,maker,breaker,claims):
        need(cell in board-maker-breaker, 'terminal Maker claim is not fresh')
        need(claims+1 <= max_claims, 'claimed Maker height exceeded')
        hit = terminal(maker|{cell},breaker,claims+1)
        need(hit is not None, 'prescribed terminal claim does not complete a selected guard')
        return dict(completion=cell,**hit)

    def walk(node,maker,breaker,claims):
        tick()
        if len(rows) >= 10000 or counts['reply_branches'] >= 100000:
            raise TimeoutError('finite replay row/reply limit exceeded')
        need(m0 <= maker and b0 <= breaker and not maker&breaker
             and maker|breaker <= board
             and len(maker-m0) == len(breaker-b0) == claims,
             'old colors, alternation or full board changed')
        need(claims < max_claims, 'claimed Maker height exceeded')
        u,kind = node['maker'],node['kind']
        need(u in board-maker-breaker, 'prescribed Maker entry is not fresh')
        need(kind in ('force','fork','dispatch'), 'unknown literal table node')
        after = maker|{u}
        row_id = len(rows)
        row = dict(node=row_id, kind=kind, maker_before=sorted(maker),
                   breaker_before=sorted(breaker), maker=u, maker_after=sorted(after),
                   additional_maker_claims=claims+1, replies=[])
        rows.append(row)
        hit = terminal(after,breaker,claims+1)
        if hit is not None:
            row['terminal'] = hit
            return row_id
        replies = legal_responses(board,after,breaker)
        need(replies, 'board exhausted without the claimed selected win')
        row['legal_replies'] = replies
        if kind == 'force':
            q,target = node['reply'],family[node['target']]
            need(not target&breaker and target-after == {q} and q in replies,
                 'forced reply lacks its exact fresh live threat')
            row.update(required_reply=q, forcing_target=node['target'])
        elif kind == 'fork':
            threats = node['threats']
            need(len(threats) == 2 and len({t['completion'] for t in threats}) == 2,
                 'fork requires two distinct completion cells')
            for threat in threats:
                target,cell = family[threat['target']],threat['completion']
                need(not target&breaker and target-after == {cell} and cell in replies,
                     'fork lacks an exact fresh live completion')
            row['threats'] = deepcopy(threats)
        else:
            explicit = [v for case in node['cases'] for v in case['replies']]
            need(len(explicit) == len(set(explicit)) and all(v in board for v in explicit),
                 'dispatch rows overlap or use nonexistent cells')
        for v in replies:
            tick(); counts['reply_branches'] += 1
            if counts['reply_branches'] > 100000:
                raise TimeoutError('finite reply limit exceeded')
            counts['outside_C30_replies'] += v not in C30
            counts['outside_witness_support_replies'] += v not in SUPPORT
            branch = dict(reply=v)
            new_breaker = breaker|{v}
            if kind == 'force' and v != node['reply']:
                branch.update(complete(node['reply'],after,new_breaker,claims+1))
            elif kind == 'fork':
                endpoints = [t['completion'] for t in node['threats']]
                cell = endpoints[1] if v == endpoints[0] else endpoints[0]
                branch.update(complete(cell,after,new_breaker,claims+1))
            else:
                if kind == 'force':
                    child = node['next']; branch['case'] = 'required_reply'
                else:
                    matching = [(i,case) for i,case in enumerate(node['cases']) if v in case['replies']]
                    need(len(matching) <= 1, 'reply has multiple dispatch continuations')
                    child = matching[0][1]['next'] if matching else node['otherwise']
                    branch['case'] = str(matching[0][0]) if matching else 'otherwise'
                branch['child'] = walk(child,after,new_breaker,claims+1)
            row['replies'].append(branch)
        need([branch['reply'] for branch in row['replies']] == replies,
             'a physical fresh reply was omitted, duplicated or reordered')
        return row_id

    root = walk(table,m0,b0,0)
    return dict(root=root, board=sorted(board), initial_maker=sorted(m0),initial_breaker=sorted(b0),
        rows=rows, counts=dict(counts), terminal_target_counts=dict(leaves_by_target),
        every_physical_fresh_reply_checked=True, no_outside_reply_quotient=True,
        no_response_after_completion=True)


def bind_state(state):
    need(state == dict(maker=sorted(M0),breaker=sorted(B0),turn='Maker'),
         'exact S9 old physical colors or turn differ')
    need(len(M0) == len(B0) == 9 and not (M0|B0)&C30 and len(C30) == 30
         and len(SUPPORT) == 22 and SUPPORT <= C30, 'C30/witness domain is not pristine')


def bind_guards(accepted,edges,tick):
    need(accepted['status'] == 'verified_partition_reduction_and_12_conditional_defenses'
         and accepted['schema'] == 'snaky-browser-twentyfourth-partition04-v2'
         and accepted['checker_sha256'] == PINS['verification/browser_twentyfourth_partition04_v2.py'],
         'wrong accepted C30 reduction')
    bind_state(accepted['binding']['physical_state'])
    need(accepted['binding']['live_targets'] == ordered(e for e in edges if not e&B0)
         and accepted['binding']['literal_target_count'] == 432
         and accepted['binding']['initial_live_count'] == 194,
         'accepted literal physical geometry differs')
    need(accepted['partition']['core_domain'] == sorted(C30), 'accepted C30 domain differs')
    core = accepted['core_reduction']
    minimal = tuple(map(frozenset,core['minimal_guards']))
    need(len(minimal) == len(set(minimal)) == 65 and core['minimal_guard_count'] == 65
         and canonical(ordered(minimal)) == core['minimal_guards_sha256'], 'accepted65-family binding differs')
    need(len(GUARDS) == 17 and len(set(GUARDS.values())) == 17
         and all(t in minimal for t in GUARDS.values()), 'a claimed guard is absent from accepted minimal65')
    redundant = frozenset((11,21,31,40,41,50))
    need(redundant not in GUARDS.values() and len(core['redundant_supersets']) == 1
         and core['redundant_supersets'][0]['supplied_guard'] == sorted(redundant),
         'attack incorrectly depends on the redundant66th guard')
    witnesses = []
    for label,target in GUARDS.items():
        tick(); edge = WITNESSES[label]
        need(edge in edges and not edge&B0 and edge&C30 == target,
             'listed full target is not a live exact C30 projection: '+label)
        missing = edge-M0-target
        if label.startswith('C'):
            need(not missing and edge-M0 == target, 'central guard is not the full fresh trace')
        else:
            need(missing == OMITTED[label] and missing and not missing&(M0|B0|C30),
                 'boundary guard omitted-cell distinction changed: '+label)
        witnesses.append(dict(label=label,guard=sorted(target),accepted_minimal_index=minimal.index(target),
            full_physical_target=sorted(edge),old_Maker_cells=sorted(edge&M0),
            fresh_omitted_cells=sorted(missing),selected_completion_alone_is_physical=not missing))
    return witnesses


def path_receipt(checked,line):
    """Follow an illustrative path through the already checked full replay."""
    node = checked['root']
    for i,(u,q) in enumerate(line):
        row = checked['rows'][node]
        need(row['maker'] == u, 'illustrative path Maker claim differs')
        if q is None:
            need(i == len(line)-1 and 'terminal' in row, 'path falsely ends before a selected completion')
            return dict(line=line,maker_final=row['maker_after'],breaker_final=row['breaker_before'],
                        **row['terminal'])
        branch = next(b for b in row['replies'] if b['reply'] == q)
        if 'completion' in branch:
            need(i+1 == len(line)-1 and line[-1] == (branch['completion'],None),
                 'illustrative path continues after an immediate completion')
            return dict(line=line,maker_final=sorted(set(row['maker_after'])|{branch['completion']}),
                breaker_final=sorted(set(row['breaker_before'])|{q}),
                **{k:v for k,v in branch.items() if k not in ('reply','completion')})
        node = branch['child']
    raise ValueError('illustrative path is incomplete')


def controls(table,edges,tick):
    out = []
    def reject(name,action):
        try: action()
        except (ValueError,StopIteration) as error:
            out.append(dict(name=name,rejected=True,reason=str(error)))
        else: raise ValueError('negative control accepted: '+name)
    reject('old_Maker_stone_cannot_be_dropped', lambda:
        bind_state(dict(maker=sorted(M0-{44}),breaker=sorted(B0),turn='Maker')))
    reject('old_Breaker_stone_cannot_be_dropped', lambda:
        bind_state(dict(maker=sorted(M0),breaker=sorted(B0-{34}),turn='Maker')))
    reject('omitted_real_outside_reply', lambda:
        legal_responses(BOARD,M0|{43},B0,sorted(BOARD-M0-B0-{43,0})))
    bad = deepcopy(table['cases'][0]['next']); bad['reply'] = 31
    reject('wrong_forced_C3_reply', lambda:
        replay(bad,GUARDS,BOARD,M0|{43},B0|{52},edges,tick,9))
    wrong_row = table['cases'][1]['next']
    reject('B52_cannot_use_B53_row', lambda:
        replay(wrong_row,GUARDS,BOARD,M0|{43},B0|{52},edges,tick,9))
    reject('claimed_first_Maker_cell', lambda:
        replay(table,GUARDS,BOARD,M0,B0|{43},edges,tick))
    badfork = fork(0,'a',1,'b',1)
    reject('fork_completions_must_differ', lambda:
        replay(badfork,{'a':frozenset((0,1)),'b':frozenset((0,2))},
               {0,1,2},set(),set(),(),tick,2))
    final = replay(fork(0,'a',1,'b',2),{'a':frozenset((0,1)),'b':frozenset((0,2))},
                   {0,1,2},set(),set(),(),tick,2)
    need(final['counts']['winning_leaves'] == final['counts']['final_available_claim_wins'] == 2,
         'both final available claims must win before a response')
    out.append(dict(name='both_final_available_claims',verified=True,replay=final))
    immediate = replay(chain([(0,1,'single')],badfork),{'single':frozenset((0,))},
                       {0},set(),set(),(),tick,1)
    need(immediate['counts'].get('reply_branches',0) == 0
         and immediate['counts']['final_available_claim_wins'] == 1,
         'immediate win must precede even an invalid nominal response')
    out.append(dict(name='immediate_terminal_before_reply',verified=True,replay=immediate))
    return out


def audit(tick):
    for path,wanted in PINS.items():
        tick(); need(sha(BASE/path) == wanted, 'changed pinned input: '+path)
    accepted = json.loads((BASE/ACCEPTED).read_text())
    for path,wanted in accepted['input_sha256'].items():
        tick(); need(sha(BASE/path) == wanted, 'changed accepted reduction dependency: '+path)
    need(accepted['certificate_file_sha256'] == PINS[CERTIFICATE]
         and accepted['certificate'] == json.loads((BASE/CERTIFICATE).read_text()),
         'accepted R/T receipt binding differs')
    edges = geometry(tick)
    witnesses = bind_guards(accepted,edges,tick)
    table = proposed_table()
    checked = replay(table,GUARDS,BOARD,M0,B0,edges,tick)
    need(checked['counts']['maximum_maker_claims'] == 10
         and checked['rows'][checked['root']]['legal_replies'] == sorted(BOARD-M0-B0-{43}),
         'height or full root-reply coverage differs')
    longest = [(43,52),(32,33),(31,42),(30,10),(51,61),(21,50),(11,40),(12,41),(14,15),(13,None)]
    selected_only = path_receipt(checked,longest)
    need(selected_only['selected_wins'] == ['k'] and not selected_only['physical_target_indices'],
         'longest boundary completion was confused with a physical Snaky win')
    p_path = path_receipt(checked,[(43,53),(32,33),(42,31),(51,52),(61,None)])
    need('p' in p_path['selected_wins'] and not p_path['physical_target_indices'],
         'B53 boundary completion distinction differs')
    return dict(status='verified_C30_seventeen_guard_selected_obstruction',
        binding=dict(physical_state=accepted['binding']['physical_state'],board_size=10,
            cell_id='10*y+x',literal_target_count=432,live_target_count=194,
            C30_domain=sorted(C30),witness_support=sorted(SUPPORT),
            accepted_minimal_guard_count=65,redundant_guard_not_used=True),
        named_guards={name:sorted(t) for name,t in GUARDS.items()},physical_witnesses=witnesses,
        literal_table=table,literal_table_sha256=canonical(table),replay=checked,
        longest_selected_only_path=selected_only,B53_selected_only_path=p_path,
        focused_controls=controls(table,edges,tick),
        scope=dict(selected_guard_family_Maker_winning=True,all_physical_fresh_B_replies=True,
            minimum_adversarial_initial_case='exact Maker-pristine C30 inherited from S9',
            arbitrary_prior_B_inside_C30_attack_not_claimed=True,
            adding_response_support_cannot_defend_same_guards=True,
            physical_S9_Maker_win_proved=False,physical_S9_Breaker_win_proved=False,
            empty_board_result=None,no_strategy_search=True,no_solver=True))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',required=True,type=Path)
    args = ap.parse_args(argv)
    need(not args.output.exists(),'fresh report required')
    cpu,wall = time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu >= 9 or time.monotonic()-wall >= 25:
            raise TimeoutError('C30_seventeen_guard_finite_limit')
    report = dict(schema='snaky-C30-seventeen-guard-independent-v1',
        checker_sha256=sha(Path(__file__)),input_sha256=PINS,
        created_utc=datetime.now(timezone.utc).isoformat())
    try: report.update(audit(tick))
    except (ValueError,KeyError,TypeError,IndexError,StopIteration,OSError,TimeoutError) as error:
        report.update(status='UNKNOWN' if isinstance(error,TimeoutError) else 'rejected',error=str(error))
    report.update(cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x') as stream:
        json.dump(report,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps({key:report.get(key) for key in ('status','error','cpu_seconds','elapsed_seconds')}))
    return int(report['status'] != 'verified_C30_seventeen_guard_selected_obstruction')


if __name__ == '__main__':
    raise SystemExit(main())
