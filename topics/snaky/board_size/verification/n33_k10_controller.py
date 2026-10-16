#!/usr/bin/env python3
"""Finite independent check of the proposed full physical N33 K10 controller.

Regenerate all literal targets, preserve the complete old colors, and check
both waiting phases and every pairing commitment. Exterior histories are
covered by the disjoint-pair invariant, not by sampled play. No search,
constructor, catalog, solver, or modification of the accepted K8 is used.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/02-twentyfirst-final.txt':
        '65be13967a79d3fd206b111c8f3e987d47dc7a11b9a1349743fab179a430cf5f',
    'browser/02-twentyfirst-prompt.txt':
        'e20e6692b7b80c1e1ccb11b882cde0e4f8ef9f25c0927c80611d7b349c957996',
    'verification/browser_sixteenth_maker02.json':
        'b4a6cddcf00d819dfc43675f7f8e83b0c328ebc9159ecd57a164194d72e6e083',
    'verification/lcap_k8_controller.py':
        '3e526e80082e733216301de30dbd052d898e10f38dc713dd8269ebf9b9dc3535',
    'verification/lcap_k8_controller.json':
        '6923ff233b8b7fa0faeaecf65c03118eccf7c6e5f2f12739d1581d70409630cf',
    'maker/earlier-pairing-row-result.pairing.json':
        '4798216f6401073a9c8830a7c65d454207268f856840d1fd5cf80732a421e8ea',
    'verification/earlier_pairing_replay.json':
        'c228eae5cc77312edba72808500acee0145660a80e83d0cf8877fec78b427fec',
    'verification/browser_eighteenth_maker.py':
        '747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
    'verification/descendant_pairing_replay.py':
        '42b67d5d9c6cac3334c563f6a762e1ff6b8fcaaedaf9e5c0828db1e28f1110eb',
}
CELLS = dict(a=(11,8), b=(13,8), c=(13,9), d=(12,9), e=(14,7),
             g=(14,8), h=(14,9), i=(14,10), j=(12,7), k=(12,8))
K_NAMES = 'abcdeghijk'
K = frozenset(CELLS.values())
K8 = K-{CELLS['j'],CELLS['k']}
UNMATCHED = frozenset(((14,1),(6,3),(9,3),(13,3),(14,4),(9,5),(4,6),
    (7,10),(6,11),(1,12),(2,13),(6,13),(7,13),(1,14),(2,14),(3,14),(6,14),(14,14)))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load(name, path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def named(names):
    return frozenset(CELLS[name] for name in names)


def expected_targets():
    rows=(('H',8,10,((13,7),(14,7)),'akbe'),
          ('H',8,10,((13,9),(14,9)),'akbch'),
          ('V',13,6,((14,9),(14,10)),'bchi'),
          ('V',14,7,((13,6),(13,7)),'eghi'),
          ('V',14,8,((13,7),(13,8)),'bghi'),
          ('H',8,9,((12,9),(13,9)),'akcd'),
          ('V',13,6,((12,9),(12,10)),'bcd'),
          ('V',12,8,((13,7),(13,8)),'bkd'),
          ('V',12,7,((13,6),(13,7)),'jkd'),
          ('H',8,9,((12,7),(13,7)),'akj'))
    result={}
    for index,(axis,fixed,start,hook,trace) in enumerate(rows,1):
        body={(start+t,fixed) if axis=='H' else (fixed,start+t) for t in range(4)}
        result[f'W{index}']=(frozenset(body|set(hook)),named(trace))
    return result


def first_policies():
    additions={name:('bc','hi') for name in 'adegj'}
    additions.update(b=('cd','hi'), c=('bd','hi'), h=('bc','gi'), i=('bc','gh'),
                     outside_unmatched=('bc','hi'))
    rows={name:dict(mode='commit',reply=CELLS['k'],pairs=tuple(named(p) for p in pairs))
          for name,pairs in additions.items()}
    rows['k']=dict(mode='phase_II',reply=CELLS['j'],pairs=())
    return rows


def waiting_safety(traces, owned, blocked, reserved):
    active=[t-owned for t in traces if not t&blocked]
    need(active and all(t and t <= reserved and len(t)>=2 for t in active),
         'waiting phase permits an immediate entry or falsely empty obligation')
    for entry in (None,*sorted(reserved)):
        after=owned if entry is None else owned|{entry}
        need(not any(t <= after for t in traces if not t&blocked),
             'Maker completes a core obligation before the waiting response')
    return dict(active_trace_count=len(active),minimum_pristine_requirement=min(map(len,active)),
                entries_including_outside=len(reserved)+1)


def commitment(traces, owned, blocked, row, reserved, literal):
    reply,pairs=row['reply'],row['pairs']
    need(reply in reserved-owned-blocked,'commitment response is not fresh and reserved')
    need(not any(t <= owned for t in traces if not t&blocked),'Maker wins before commitment response')
    literal.pairing(pairs,reserved-owned-blocked-{reply})
    remaining=[]
    for trace in traces:
        if trace&(blocked|{reply}):
            continue
        residual=trace-owned
        need(residual and any(p <= residual for p in pairs),
             f'unprotected commitment residual: {sorted(residual)}')
        remaining.append(residual)
    need(remaining,'unexpected empty committed obligation family')
    return tuple(remaining)


def admission(declared,maker,breaker,original,exterior,domain,first,second,geometry,literal,guard):
    literal.bind_state(declared,maker,breaker,33)
    need(domain==K and domain <= literal.V-maker-breaker,'wrong or nonpristine K10 domain')
    need(len(original)==54 and len(exterior)==51,'wrong original/exterior pair count')
    literal.pairing(original,literal.V-maker-breaker)
    endpoints=literal.pairing(exterior,literal.V-maker-breaker-domain)
    removed=frozenset(named(p) for p in ('be','ch','gi'))
    need(removed <= set(original) and set(exterior)==set(original)-removed,'changed exterior matching')
    need(literal.V-maker-breaker-domain-endpoints == UNMATCHED,'unmatched exterior inventory differs')
    need(len(geometry)==1040 and not any(edge <= maker for edge in geometry),'geometry or initial Maker win')
    live=tuple(edge for edge in geometry if not edge&breaker)
    inventory,uncovered=[],[]
    for edge in sorted(live,key=lambda t:sorted(t)):
        guard(); hits=[j for j,p in enumerate(exterior) if p <= edge]
        trace=edge&domain
        if not hits: uncovered.append((edge,trace))
        inventory.append(dict(target=sorted(edge),exterior_pair_indices=hits,reserved_trace=sorted(trace)))
    expected=expected_targets()
    need(set(uncovered)==set(expected.values()) and len(uncovered)==10,'ten-target no-Q inventory differs')
    for name,(edge,_) in expected.items():
        outside=edge-maker-domain
        want={(14,11)} if name=='W5' else {(12,11)} if name=='W8' else set()
        need(outside==want,'unowned exterior target cells were silently removed: '+name)
    traces=tuple(t for _,t in uncovered)
    wait_I=waiting_safety(traces,frozenset(),frozenset(),K)
    need(wait_I['minimum_pristine_requirement']==3,'first-stage minimum trace size differs')
    wait_II=waiting_safety(traces,named('k'),named('j'),K8)
    need(wait_II['minimum_pristine_requirement']==2,'second-stage minimum trace size differs')
    need(set(first)==set(K_NAMES)|{'outside_unmatched'},'missing first-phase entry/outside row')
    need(set(second)==set('abcdeghi')|{'outside_unmatched'},'missing second-phase entry/outside row')
    commitments={}
    for name,row in first.items():
        entered=frozenset() if name=='outside_unmatched' else named(name)
        if name=='k':
            need(row==dict(mode='phase_II',reply=CELLS['j'],pairs=()),'wrong actual Mk/Bj transition')
            continue
        need(row['mode']=='commit' and row['reply']==CELLS['k'],'first phase does not commit by actual Bk')
        residual=commitment(traces,entered,frozenset(),row,K,literal)
        commitments['I:'+name]=(row,residual)
    need(set(first['outside_unmatched']['pairs'])=={named('bc'),named('hi')},'wrong first exterior commitment')
    for name,row in second.items():
        entered=frozenset() if name=='outside_unmatched' else named(name)
        need(row['mode']=='commit','second phase does not end in a commitment')
        residual=commitment(traces,named('k')|entered,named('j'),row,K,literal)
        commitments['II:'+name]=(row,residual)
    need(second['outside_unmatched']['reply']==CELLS['d']
         and set(second['outside_unmatched']['pairs'])==removed,'wrong second exterior commitment')
    return live,uncovered,inventory,commitments,dict(I=wait_I,II=wait_II)


def committed_replay(targets,pairs,guard):
    """Protect residual core requirements under every move/filler interleaving.

    Actual owned/blocked cells have already been removed by commitment().
    Irrelevant core cells and all exterior cells are the outside symbol 0.
    Every fresh active-cell filler is allowed, a strengthening of the specified
    lexicographically least physical filler. No physical pass is prescribed.
    """
    need(targets and all(t for t in targets),'empty residual is a win, not an exhausted safe family')
    domain=frozenset().union(*targets,*pairs)
    need(len(domain)<=7,'unexpected residual replay domain')
    positions={q:1<<j for j,q in enumerate(sorted(domain))}
    masks=tuple(sum(positions[q] for q in t) for t in targets)
    pmasks=tuple(sum(positions[q] for q in p) for p in pairs)
    universe=(1<<len(domain))-1
    pending,seen=[(0,0)],set()
    entries=fillers=final=0
    def bits(mask):
        while mask:
            bit=mask&-mask; yield bit; mask^=bit
    while pending:
        guard(); m,b=pending.pop()
        if (m,b) in seen: continue
        seen.add((m,b)); need(len(seen)<=5000,'unexpected replay state bound')
        for move in (0,*bits(universe&~(m|b))):
            nm=m|move
            need(not any(t&nm==t for t in masks),'Maker wins before the committed response')
            free=universe&~(nm|b)
            final+=bool(move and not free)
            mate=next((p^move for p in pmasks if move and p&move and (p^move)&free),0)
            responses=(mate,) if mate else (0,*bits(free))
            for response in responses:
                if (nm,b|response) not in seen: pending.append((nm,b|response))
                fillers+=not mate
            entries+=1
    return dict(domain=sorted(domain),states=len(seen),maker_entries_including_outside=entries,
                arbitrary_filler_transitions=fillers,final_local_maker_claim_checks=final)


def waiting_pair_invariant():
    cases=[]
    for before in product(range(3),repeat=2):
        if 1 in before and 2 not in before: continue
        for x in (0,1):
            if before[x]: continue
            after=list(before); after[x]=1
            need(after!=[1,1],'exterior Maker finishes a pair before response')
            if after[1-x]==0:
                after[1-x]=2; action='actual_mate_and_keep_waiting'
            else:
                need(after[1-x]==2,'fresh exterior entry has Maker-owned mate')
                action='commit_by_fresh_reserved_reply'
            need(2 in after,'waiting action lost the exterior blocking invariant')
            cases.append(dict(before=before,maker_endpoint=x,after=after,action=action))
    return cases


def initial_entry_table(maker,breaker,reserved,rows,exterior,geometry,literal):
    table=[]
    for entry in sorted(literal.V-maker-breaker):
        need(not any(e <= maker|{entry} for e in geometry),'actual first entry wins before response')
        if entry in reserved:
            name=next(n for n,q in CELLS.items() if q==entry); row=rows[name]
            reply,action=row['reply'],row['mode']+':'+name
        else:
            mate=next((next(iter(p-{entry})) for p in exterior if entry in p),None)
            if mate is not None and mate not in maker|breaker:
                reply,action=mate,'actual_Q_mate_and_wait'
            else:
                reply,action=rows['outside_unmatched']['reply'],'commit:outside_unmatched'
        need(reply in literal.V-maker-breaker-{entry},'literal first-entry response is not fresh')
        table.append(dict(maker_entry=entry,breaker_reply=reply,action=action))
    return table


def audit(guard):
    for path,digest in PINS.items():
        guard(); need(sha(BASE/path)==digest,'changed pinned input: '+path)
    k8=load('n33_accepted_k8',BASE/'verification/lcap_k8_controller.py')
    literal=load('n33_literal_geometry',BASE/'verification/browser_eighteenth_maker.py')
    pairing=load('n33_literal_pairing',BASE/'verification/descendant_pairing_replay.py')
    geometry=literal.literal_geometry(guard)
    accepted=json.loads((BASE/'verification/browser_sixteenth_maker02.json').read_text())
    old=json.loads((BASE/'verification/lcap_k8_controller.json').read_text())
    maker=literal.CROSS_M-{(13,8),(13,9),(11,8),(12,8)}
    breaker=literal.CROSS_B-{(14,7),(14,9),(12,9),(12,7)}
    declared=accepted['parent']; literal.bind_state(declared,maker,breaker,33)
    prompt=(BASE/'browser/02-twentyfirst-prompt.txt').read_text()
    states=[json.loads(line) for line in prompt.splitlines() if line.startswith('{"board":')]
    need(len(states)==1,'prompt has no unique full physical state')
    literal.bind_state(dict(states[0],stones_each=33),maker,breaker,33)
    literal.bind_state(accepted['residuals']['L_cap'],maker|named('k'),breaker|named('j'),34)
    need(old['status']=='independently_verified_full_conditional_breaker_controller'
         and old['complete_defense'] is True and old['source_sha256']==PINS['verification/lcap_k8_controller.py'],
         'accepted K8 report is not bound to its unchanged source')
    literal.bind_state(old['original_state'],maker|named('k'),breaker|named('j'),34)
    certificate=json.loads((BASE/'maker/earlier-pairing-row-result.pairing.json').read_text())
    checked=pairing.check_certificate(certificate,maker|named('ka'),breaker|named('jd'),geometry,literal,guard)
    need(len(checked['pairs'])==54 and checked['live_target_count']==257,'accepted L_row coverage changed')
    original=tuple(pairing.physical(p) for p in certificate['pairs'])
    removed={named(p) for p in ('be','ch','gi')}
    exterior=tuple(p for p in original if p not in removed)
    first=first_policies(); second={n:dict(mode='commit',**r) for n,r in k8.policies().items()}
    need(exterior==tuple(frozenset(map(tuple,p)) for p in old['exterior_pairs']),'K8 exterior matching differs')
    for name,row in second.items():
        bound=old['policy'][name]
        need(tuple(bound['breaker_reply'])==row['reply']
             and tuple(frozenset(map(tuple,p)) for p in bound['replacement_pairs'])==row['pairs'],
             'second-phase literal policy differs from accepted K8')
    live,uncovered,inventory,commitments,waiting=admission(declared,maker,breaker,original,exterior,K,
                                                        first,second,geometry,literal,guard)
    phase_II={(edge,edge&K8) for edge,_ in uncovered if CELLS['j'] not in edge}
    bound_II={(frozenset(map(tuple,r['target'])),frozenset(map(tuple,r['trace'])))
              for r in old['targets_without_exterior_pair']}
    need(phase_II==bound_II,'upstream-to-K8 target obligations differ')
    local={name:committed_replay(residual,row['pairs'],guard)
           for name,(row,residual) in commitments.items()}
    q_wait=waiting_pair_invariant(); q_committed=k8.pair_invariant()
    entries_I=initial_entry_table(maker,breaker,K,first,exterior,geometry,literal)
    entries_II=initial_entry_table(maker|named('k'),breaker|named('j'),K8,second,exterior,geometry,literal)
    need(len(entries_I)==130 and len(entries_II)==128,'literal initial move coverage differs')
    controls=[]
    def reject(name,fn):
        guard()
        try: fn()
        except ValueError: controls.append(name)
        else: raise ValueError('negative control accepted: '+name)
    def altered(**changes):
        args=dict(declared=declared,maker=maker,breaker=breaker,original=original,exterior=exterior,
            domain=K,first=first,second=second,geometry=geometry,literal=literal,guard=guard)
        args.update(changes); return admission(**args)
    reject('dropped_old_Maker',lambda:altered(maker=maker-{min(maker)}))
    reject('dropped_old_Breaker',lambda:altered(breaker=breaker-{min(breaker)}))
    reject('same_count_changed_old_Maker',lambda:altered(maker=(maker-{min(maker)})|named('k')))
    reject('omitted_reserved_j',lambda:altered(domain=K-named('j')))
    reject('overlapping_exterior_pair',lambda:altered(exterior=exterior[:-1]+(exterior[0],)))
    bad=deepcopy(first); del bad['j']; reject('missing_first_entry',lambda:altered(first=bad))
    bad=deepcopy(first); bad['k']['reply']=CELLS['a']; reject('wrong_actual_K8_transition',lambda:altered(first=bad))
    bad=deepcopy(first); bad['a']['reply']=CELLS['a']; reject('stale_first_response',lambda:altered(first=bad))
    bad=deepcopy(first); bad['b']['pairs']=(named('bc'),named('hi'))
    reject('pair_contains_Maker_entry',lambda:altered(first=bad))
    bad=deepcopy(first); bad['c']['pairs']=(); reject('uncovered_after_commitment',lambda:altered(first=bad))
    bad=deepcopy(first); bad['outside_unmatched']['pairs']=(named('bc'),)
    reject('incomplete_outside_commitment',lambda:altered(first=bad))
    bad=deepcopy(second); del bad['d']; reject('missing_second_entry',lambda:altered(second=bad))
    bad=deepcopy(second); bad['d']['reply']=CELLS['d']; reject('stale_second_response',lambda:altered(second=bad))
    reject('one_cell_waiting_obligation',lambda:waiting_safety((named('a'),),frozenset(),frozenset(),K))
    reject('empty_projection_is_not_safe',lambda:committed_replay((frozenset(),),(),guard))
    reject('unpaired_immediate_completion',lambda:committed_replay((named('a'),),(),guard))
    final=committed_replay((named('ab'),),(named('ab'),),guard)
    need(final['final_local_maker_claim_checks']>0,'final local claim is not checked')
    guard()
    encode=lambda rows:{n:dict(mode=r['mode'],reply=r['reply'],pairs=[sorted(p) for p in r['pairs']]) for n,r in rows.items()}
    return dict(status='independently_verified_full_conditional_N33_breaker_controller',complete_defense=True,
        original_state={k:v for k,v in declared.items() if k!='status'},reserved_names=CELLS,reserved_domain=sorted(K),
        geometry_count=len(geometry),live_target_count=len(live),initial_free_count=130,
        original_pair_count=54,exterior_pairs=[sorted(p) for p in exterior],unmatched_exterior=sorted(UNMATCHED),
        full_live_target_inventory=inventory,targets_without_exterior_pair=[dict(name=n,target=sorted(e),trace=sorted(t))
            for n,(e,t) in expected_targets().items()],phase_I_policy=encode(first),phase_II_policy=encode(second),
        phase_I_initial_entries=entries_I,phase_II_initial_entries=entries_II,waiting_safety=waiting,
        commitment_replays=local,waiting_pair_color_controls=q_wait,committed_pair_invariant=q_committed,
        negative_controls=controls,final_claim_control=final,accepted_K8_state_exactly_recovered=True,
        response_rule='Wait with actual Q-mate responses only. A first K10 entry other than k or an exterior '
            'entry without a required free mate commits by Bk to Table I. Mk/Bj enters the pristine K8 phase, '
            'using its exact Table II or unmatched-exterior commitment Bd. After commitment take a fresh '
            'selected-pair mate; otherwise take the lexicographically least free physical cell (x then y), '
            'if any. All old and intermediate physical stones persist. No pass or virtual claim is used.',
        scope='Complete ordinary physical Breaker defense only at the exact Maker-to-move N33 33+33 state. '
            'No earlier-state loss, empty-board result, board-size bound, or novelty claim follows.')


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(); need(not args.output.exists(),'fresh report required')
    wall,cpu=time.monotonic(),time.process_time()
    def guard():
        if time.process_time()-cpu>=8 or time.monotonic()-wall>=25:
            raise TimeoutError('finite K10 controller cap')
    try: result=audit(guard)
    except TimeoutError as error: result=dict(status='incomplete',complete_defense=False,reason=str(error))
    except (ValueError,KeyError,TypeError) as error: result=dict(status='rejected',complete_defense=False,reason=str(error))
    result.update(schema='snaky-independent-n33-k10-controller-v1',source_sha256=sha(Path(__file__)),
        input_sha256=PINS,utc=datetime.now(timezone.utc).isoformat(),cpu_seconds=time.process_time()-cpu,
        elapsed_seconds=time.monotonic()-wall,limits=dict(cpu_seconds=8,wall_seconds=25))
    with args.output.open('x') as stream: json.dump(result,stream,indent=2,sort_keys=True); stream.write('\n')
    print(json.dumps({k:result.get(k) for k in ('status','complete_defense','live_target_count','cpu_seconds','elapsed_seconds')}))
    return int(not result['complete_defense'])


if __name__=='__main__':
    raise SystemExit(main())
