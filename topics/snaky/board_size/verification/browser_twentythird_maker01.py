#!/usr/bin/env python3
"""Literal audit of two R_gap continuation obstructions and a mate-policy fork.

No solver, matching search, or tactic search is used. All old physical colors
and all 1040 targets are retained. The matching obstruction is not a Maker
win; the physical attack applies only after the explicitly stated history.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import time

import browser_eighteenth_maker as literal

BASE=Path(__file__).resolve().parents[1]
ACCEPTED='verification/browser_twentysecond_maker01.json'
PINS={
    ACCEPTED:'f06ccf683b1aa33e8342863a13783be80f85b6a4a83761bd8926ea04f3e6ad55',
    'verification/browser_twentysecond_maker01.py':'830dd76c8a121a777e9ecb033bcb6dda00f1dbe7f1a7c9f075696efb52837b9e',
    'verification/browser_twentieth_maker01.json':'748e13d9613d94a2017d12588bd5233e315aea7f834acad48e730e7b64bcb76e',
    'verification/browser_twentieth_maker01.py':'98fd60920a6f67ed3560debaced2324bb5493cf1e5ba52406ace71d00d91241a',
    'verification/browser_eighteenth_maker.py':'747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
    'browser/01-twentythird-final.txt':'cd81878bb8a8f40eb2245942aeb1222cb9f0e72241ec4eaf9b2096c9d8918191',
    'browser/01-twentythird-final-main.txt':'22a6bbbbdabc4b4136b85b7447647e26a210eeeffd1f4589557690f07d767f95',
    'browser/01-twentythird-prompt.txt':'9b7922aa49d6ee95d89953cf9872bdb2e7de91922d9fb1e64ed9632962055985',
}
M0=frozenset(((3,11),(4,4),(4,7),(4,8),(4,9),(5,5),(5,6),(5,8),(6,3),
    (6,5),(6,8),(7,2),(7,3),(7,5),(7,6),(7,7),(7,8),(8,6),(8,8),(9,8),
    (9,11),(10,5),(10,6),(10,7),(10,8),(10,9),(11,5)))
B0=frozenset(((3,7),(3,9),(4,5),(4,6),(4,10),(5,3),(5,4),(5,7),(5,9),
    (6,4),(6,7),(6,9),(7,4),(7,9),(8,4),(8,7),(8,9),(9,3),(9,5),(9,6),
    (9,7),(9,9),(10,10),(11,4),(11,6),(11,7),(11,9)))
RIGHT_HISTORY=(((10,13),(9,13)),((11,13),(11,14)),((12,13),(12,14)),
    ((13,13),(13,14)),((13,12),(14,12)))
LEFT_HISTORY=(((2,11),(1,11)),((2,12),(1,12)),((2,13),(1,13)),
    ((4,11),(5,11)),((4,12),(5,12)),((4,13),(5,13)))
LEFT_PAIR_IDS=(35,43,48,36,44,49)
CELLS=dict(zip('abcdefghi',((10,11),(11,12),(12,12),(13,11),(14,11),
    (14,13),(13,10),(14,14),(13,9))))
RESIDUAL_LABELS=('bf','abc','bcde','dfgh','cdgi')
FORK_PIVOT=(3,10)
COMPLETIONS=((2,14),(4,14))
INTERVENTIONS=frozenset((FORK_PIVOT,*COMPLETIONS))


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()


def cells(raw):
    need(isinstance(raw,list) and all(isinstance(q,list) and len(q)==2
        and all(type(v) is int and 1<=v<=14 for v in q) for q in raw),'nonliteral physical cells')
    result=frozenset(map(tuple,raw));need(len(result)==len(raw),'duplicate cell');return result


def points(values):return [list(q) for q in sorted(values)]


def named(labels):return frozenset(CELLS[x] for x in labels)


def state(m,b,turn='Maker'):
    return dict(board=[1,1,14,14],maker=points(m),breaker=points(b),turn=turn,
        maker_count=len(m),breaker_count=len(b))


def target(direction,fixed,start,hook):
    body=frozenset((start+i,fixed) if direction=='R' else (fixed,start+i) for i in range(4))
    tail=frozenset(hook);return body|tail,(body,tail)


def witness(geometry,direction,fixed,start,hook):
    edge,parts=target(direction,fixed,start,hook)
    need(geometry.get(edge)==parts,'wrong literal full witness');return edge


def advance(m,b,u,v,geometry):
    need(u in literal.V-m-b and v in literal.V-m-b-{u},'stale physical claim or reply')
    need(not any(e<=m|{u} for e in geometry),'Maker already won before proposed reply')
    return m|{u},b|{v}


def preserve(family,m,b,pairs):
    literal.pairing(pairs,literal.V-m-b)
    need(all(e&b or any(p<=e for p in pairs) for e in family),'lost protected full target')


def bind(source,geometry,tick):
    need(source['status']=='verified_63pair_partial_defense_and_conditional_switch'
        and source['source_sha256']==PINS['verification/browser_twentysecond_maker01.py']
        and source['geometry_count']==1040 and source['full_physical_defense'] is False,
        'wrong accepted partial-defense source')
    literal.bind_state(source['original_state'],M0,B0,27)
    old=json.loads((BASE/'verification/browser_twentieth_maker01.json').read_text())
    need(old['original_state']==source['original_state']
        and old['source_sha256']==PINS['verification/browser_twentieth_maker01.py'],
        'earlier actual full state differs')
    pairs=tuple(cells(p) for p in source['classification']['pairs'])
    endpoints=literal.pairing(pairs,literal.V-M0-B0)
    need(len(pairs)==63 and len(endpoints)==126,'wrong original63 pairs')
    live={e for e in geometry if not e&B0}
    protected={e for e in live if any(p<=e for p in pairs)}
    residuals={int(r['id'][1:]):cells(r['target']) for r in source['classification']['residuals']}
    need(len(live)==385 and len(protected)==370 and set(residuals)==set(range(1,16))
        and set(residuals.values())==live-protected,'wrong full15 exception family')
    need(cells(source['classification']['unmatched_fresh'])==literal.V-M0-B0-endpoints,
        'wrong pristine unmatched cells')
    m,b=M0,B0;active=pairs
    for index,(u,v) in enumerate(RIGHT_HISTORY):
        tick();m,b=advance(m,b,u,v,geometry)
        if index<4:need(frozenset((u,v)) in active,'right prefix is not the accepted mate')
        active=tuple(p for p in active if not p&(m|b))
        if index==4:
            released=frozenset(((14,9),(14,11)))
            need(released in active,'missing accepted switch release')
            active=tuple(p for p in active if p!=released)+(frozenset(((13,11),(14,9))),)
        preserve(protected,m,b,active)
    final=source['conditional_switch'];literal.bind_state(final['final_state'],m,b,32)
    need(len(active)==57 and tuple(cells(p) for p in final['final_pairs'])==active,
        'accepted exact-history pairs differ')
    need([(tuple(r['maker']),tuple(r['breaker'])) for r in final['history']]==list(RIGHT_HISTORY),
        'accepted right history changed')
    need(not any(e<=M0 for e in geometry),'initial physical Maker win')
    return pairs,protected,residuals,m,b,active


def forced_exchange(m,b,u,v,edge,geometry,tick):
    need(edge in geometry and not edge&b and edge-m==frozenset((u,v)),
        'full target does not force the declared reply')
    nm,nb=advance(m,b,u,v,geometry);bad=[]
    for q in sorted(literal.V-nm-b):
        tick()
        if q==v:continue
        need(v in literal.V-nm-b-{q} and edge<=nm|{v} and not edge&(b|{q}),
            'off-line reply evades immediate full-target completion')
        bad.append(q)
    return nm,nb,dict(entry=u,only_surviving_reply=v,full_target=points(edge),
        legal_replies=len(bad)+1,losing_replies=points(bad),win_before_further_reply=True,
        resulting_state=state(nm,nb))


def matching_chain(family,free):
    need(len(family)==5,'five exact obligations required')
    expected=(named('bf'),named('ac'),named('de'),named('gh'))
    used=frozenset();rows=[]
    for index,edge in enumerate(family):
        need(edge<=free,'matching obligation contains nonfresh cell')
        choices={frozenset(p) for p in combinations(sorted(edge-used),2)}
        if index<4:
            need(choices=={expected[index]},'claimed forced pair is not unique')
            rows.append(dict(obligation=index+1,forced_pair=points(expected[index])));used|=expected[index]
        else:need(not choices and len(edge-used)==1,'last obligation still admits a disjoint pair')
    return dict(forced_pairs=rows,last_available=points(family[-1]-used),
        arbitrary_exterior_pairs_cannot_help=True)


def right_checks(pairs,protected,residuals,m,b,active,geometry,tick):
    t14=witness(geometry,'R',13,10,((9,12),(10,12)))
    need(t14==residuals[14],'T14 identity changed')
    m4=M0|{u for u,v in RIGHT_HISTORY[:4]};b4=B0|{v for u,v in RIGHT_HISTORY[:4]}
    _,_,t15forcing=forced_exchange(m4,b4,(13,12),(14,12),residuals[15],geometry,tick)
    mr,br,forcing=forced_exchange(m,b,(10,12),(9,12),t14,geometry,tick)
    specs=(('R',13,11,((10,12),(11,12))),('R',12,10,((9,11),(10,11))),
        ('R',12,10,((13,11),(14,11))),('C',13,10,((14,13),(14,14))),
        ('C',13,9,((12,12),(12,13))))
    edges=tuple(witness(geometry,*s) for s in specs)
    family=tuple(named(s) for s in RESIDUAL_LABELS)
    old_ids=((46,),(46,),(42,46),(42,59),(40,42));full=[]
    for index,(edge,needles,ids) in enumerate(zip(edges,family,old_ids),1):
        tick();need(edge in protected and not edge&br and edge-mr==needles,'wrong full matching residual')
        actual=tuple(i+1 for i,p in enumerate(pairs) if p<=edge)
        need(actual==ids,'original protected-pair identity differs')
        full.append(dict(id='E'+str(index),target=points(edge),old_Maker=points(edge&mr),
            required_free=points(needles),original_pair_ids=actual))
    chain=matching_chain(family,literal.V-mr-br)
    deletion=(('bc','dg'),('bf','ce','dg'),('bf','ac','dg'),('bf','ac','de','gi'),('bf','ac','de','gh'))
    for omitted,encoded in enumerate(deletion):
        ps=tuple(named(p) for p in encoded);literal.pairing(ps,literal.V-mr-br)
        need(all(i==omitted or any(p<=e for p in ps) for i,e in enumerate(family)),
            'displayed deletion control does not cover other four obligations')
    table={x:('b',('dg',)) for x in 'acefhi'}
    table.update(b=('f',('ac','de','gi')),d=('b',('gh','ci')),g=('b',('df','ci')))
    table_rows=[]
    for name,(reply,encoded) in table.items():
        tick();u,v=CELLS[name],CELLS[reply];ps=tuple(named(p) for p in encoded)
        need(u!=v and not any(e<={u} for e in family),'selected game wins before first reply')
        literal.pairing(ps,frozenset(CELLS.values())-{u,v})
        need(all(v in e or any(p<=e for p in ps) for e in family),'selected adaptive row fails')
        table_rows.append(dict(entry=u,reply=v,pairs=[points(p) for p in ps]))
    ml,bl,other_forcing=forced_exchange(m,b,(9,12),(10,12),t14,geometry,tick)
    retired=(pairs[45],pairs[62]);ql=tuple(p for p in active if p not in retired)
    need(pairs[62]==frozenset(((8,10),(9,12))) and len(ql)==55,'wrong asymmetric retirement')
    preserve(protected,ml,bl,ql)
    incidences=sorted((e for e in geometry if pairs[62]<=e),key=lambda e:sorted(e))
    need(len(incidences)==4 and all(e&b for e in incidences),'P63 exact four blocked exposures differ')
    remaining=sorted(i for i,e in residuals.items() if not e&bl)
    need(remaining==[1,2,5,6,7,8,9,10,11],'other T14 branch exception inventory differs')
    uncovered={e for e in geometry if not e&bl and not any(p<=e for p in ql)}
    need(uncovered=={residuals[i] for i in remaining},'other branch has an omitted full physical gap')
    return dict(T15_forcing=t15forcing,right=forcing,five_full_obligations=full,
        fresh_matching_contradiction=chain,inclusion_minimal_deletion_pairings=deletion,
        selected_nine_cell_adaptive_table=table_rows,selected_table_is_not_full_physical_defense=True,
        other=other_forcing,other_pairs=[points(p) for p in ql],other_remaining_exceptions=remaining,
        retired_P63_full_incidences=[dict(target=points(e),actual_Breaker_hits=points(e&b)) for e in incidences]),family


def terminal_fork(m,b,geometry,targets,tick):
    need(FORK_PIVOT in literal.V-m-b,'fork pivot is not fresh')
    nm=m|{FORK_PIVOT}
    need(not any(e<=nm for e in geometry),'declared two-step fork already wins immediately')
    for edge,z in zip(targets,COMPLETIONS):
        need(edge in geometry and not edge&b and edge-nm=={z},'wrong full physical fork requirement')
    rows=[]
    for q in sorted(literal.V-nm-b):
        tick();index=1 if q==COMPLETIONS[0] else 0;z=COMPLETIONS[index];edge=targets[index]
        need(z in literal.V-nm-b-{q} and edge<=nm|{z} and not edge&(b|{q}),
            'a legal Breaker reply evades the full-target fork')
        rows.append(dict(reply=q,winning_claim=z,full_witness=index+6))
    need(rows,'physical fork has no legal replies')
    return rows


def left_checks(pairs,protected,residuals,geometry,tick):
    m,b=M0,B0;active=pairs;records=[]
    for index,(u,v) in enumerate(LEFT_HISTORY):
        tick();need(pairs[LEFT_PAIR_IDS[index]-1]==frozenset((u,v)),'wrong original mate in left prefix')
        need(u in literal.V-m-b,'stale Maker entry')
        nm=m|{u}
        need(all(e&b or len(e-nm)>1 for e in residuals.values()),'late-repair policy could activate before prescribed mate')
        m,b=advance(m,b,u,v,geometry)
        active=tuple(p for p in active if not p&(m|b));preserve(protected,m,b,active)
        records.append(dict(round=index+1,maker=u,breaker=v,remaining_active_pairs=len(active)))
    need(residuals[6]-m=={FORK_PIVOT,COMPLETIONS[0]} and residuals[7]-m=={FORK_PIVOT,COMPLETIONS[1]},
        'two left exceptions have wrong residuals')
    need(residuals[1]-m=={(2,10),(3,13),(3,14)} and (5,11) in residuals[8]&b,
        'other displayed exception statuses differ')
    need(FORK_PIVOT not in set().union(*pairs),'activation pivot is not originally unmatched')
    targets=(residuals[6],residuals[7]);terminals=terminal_fork(m,b,geometry,targets,tick)
    pending_m=M0|{u for u,v in LEFT_HISTORY};pending_b=B0|{v for u,v in LEFT_HISTORY[:5]}
    need(len(pending_m)==33 and len(pending_b)==32,'wrong pending-sixth-reply parity')
    bad=[];total=0
    for q in sorted(literal.V-pending_m-pending_b):
        tick()
        if q in INTERVENTIONS:
            need(q==FORK_PIVOT or any(q in e for e in targets),'claimed intervention fails to block this fork')
            continue
        rows=terminal_fork(pending_m,pending_b|{q},geometry,targets,tick)
        bad.append(dict(sixth_reply=q,all_following_replies=len(rows)));total+=len(rows)
    edge=witness(geometry,'R',13,4,((3,12),(4,12)))
    need(edge in protected and pairs[48]<=edge,'released-pair dependency is not in old G')
    retained=tuple(pairs[i-1] for i in (50,60,61))
    need(set(retained)=={frozenset(((7,13),(8,13))),frozenset(((3,12),(3,13))),
        frozenset(((6,12),(6,13)))},'wrong three retained dependency pairs')
    alternatives=[]
    for q in sorted(INTERVENTIONS):
        nb=pending_b|{q};free=literal.V-pending_m-nb
        need(not edge&nb and edge-pending_m=={(3,12),(5,13),(6,13),(7,13)},'dependency target altered')
        used=literal.pairing(retained,free)
        need(all(not p<=edge for p in retained) and (edge-pending_m)-used=={(5,13)},
            'retained three pairs do not obstruct every new covering pair')
        alternatives.append(dict(reply=q,state=state(pending_m,nb),target=points(edge),
            exact_free_requirement=points(edge-pending_m),unallocated_requirement=[[5,13]]))
    return dict(class_definition='Follow original mates while entries are matched and no live exception has a one-cell threat; arbitrary adaptation allowed only at activation.',
        prefix=records,after_six_rounds=state(m,b),fork_pivot=FORK_PIVOT,
        full_fork_targets=[points(e) for e in targets],all_terminal_replies=terminals,
        exact_pending_sixth_reply=state(pending_m,pending_b,'Breaker'),
        only_replies_stopping_this_fork=points(INTERVENTIONS),all_other_sixth_replies=bad,
        following_terminal_reply_count=total,necessary_pair_release_ids=[50,60,61],
        dependency_pairs=[points(p) for p in retained],three_intervention_states=alternatives,
        unrestricted_Maker_win=False,retaining_three_pairs_cannot_restore_G_matching=True)


def audit(tick):
    for name,digest in PINS.items():tick();need(sha(BASE/name)==digest,'changed pinned input: '+name)
    source=json.loads((BASE/ACCEPTED).read_text());geometry=literal.literal_geometry(tick)
    need(len(geometry)==1040,'wrong full physical target universe')
    pairs,protected,residuals,m,b,active=bind(source,geometry,tick)
    right,family=right_checks(pairs,protected,residuals,m,b,active,geometry,tick)
    left=left_checks(pairs,protected,residuals,geometry,tick)
    controls=[]
    def reject(name,operation):
        tick()
        try:operation()
        except ValueError:controls.append(name);return
        raise ValueError('negative control accepted: '+name)
    for color,point in (('maker',[3,11]),('breaker',[5,3])):
        bad=deepcopy(source);bad['original_state'][color].remove(point)
        reject('lost_old_'+color,lambda raw=bad:bind(raw,geometry,tick))
    reject('deleted_obstruction_target',lambda:matching_chain(family[:-1],literal.V))
    reject('wrong_forced_chain',lambda:matching_chain((family[0]|named('i'),)+family[1:],literal.V))
    reject('occupied_matching_requirement',lambda:matching_chain(family,literal.V-named('b')))
    reject('overlapping_deletion_pairs',lambda:literal.pairing((named('bf'),named('bc')),literal.V))
    reject('self_reply',lambda:advance(m,b,(10,12),(10,12),geometry))
    reject('missing_T14_requirement',lambda:forced_exchange(m,b,(10,12),(8,12),residuals[14],geometry,tick))
    broken=dict(geometry);del broken[residuals[6]]
    lm=M0|{u for u,v in LEFT_HISTORY};lb=B0|{v for u,v in LEFT_HISTORY}
    reject('dropped_full_fork_target',lambda:terminal_fork(lm,lb,broken,(residuals[6],residuals[7]),tick))
    reject('fork_after_pivot_blocked',lambda:terminal_fork(lm,lb|{FORK_PIVOT},geometry,(residuals[6],residuals[7]),tick))
    reject('fork_after_endpoint_blocked',lambda:terminal_fork(lm,lb|{COMPLETIONS[0]},geometry,(residuals[6],residuals[7]),tick))
    return dict(status='verified_finite_Rgap_continuation_obstructions',geometry_count=1040,
        original_state=state(M0,B0),accepted_five_round_state=state(m,b),
        original_protected_target_count=len(protected),original_pairs=[points(p) for p in pairs],
        forced_T14_and_matching_obstruction=right,late_repair_policy_obstruction=left,
        negative_controls=controls,no_solver_or_search=True,empty_board_result=False,
        complete_conditional_parent_result=False,Lean_checked=False,
        scope='Unrestricted fresh matching is impossible at the exact right33+33 continuation. The other33+33 continuation preserves G but leaves nine exceptions. The explicit left physical attack refutes only the stated late-repair mate policy or continuations of its fixed prefix. Neither is an unrestricted parent Maker-win or Breaker-defense theorem.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();need(not args.output.exists(),'preserve previous report')
    cpu,wall=time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu>=4 or time.monotonic()-wall>=20:raise TimeoutError('finite Rgap audit cap')
    try:result=audit(tick)
    except TimeoutError as error:result=dict(status='UNKNOWN',reason=str(error))
    except (ValueError,KeyError,TypeError,IndexError,OSError) as error:result=dict(status='rejected',reason=str(error))
    result.update(schema='snaky-browser-twentythird-maker01-v1',source_sha256=sha(Path(__file__)),
        input_sha256=PINS,process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall,
        utc=datetime.now(timezone.utc).isoformat())
    with args.output.open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:result.get(k) for k in ('status','reason','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_finite_Rgap_continuation_obstructions')


if __name__=='__main__':raise SystemExit(main())
