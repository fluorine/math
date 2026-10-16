#!/usr/bin/env python3
"""Independent finite audit of a 63-pair partial physical defense and switch.

All 1040 full targets and all actual colors are retained. The 15 exceptions and
five-round override are literal proposals; no solver or game search is used.
The switch is certified only at its stated history, never at a pristine core.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

import browser_eighteenth_maker as literal
import browser_twentieth_maker01 as old

BASE = Path(__file__).resolve().parents[1]
ACCEPTED = 'verification/browser_twentieth_maker01.json'
PINS = {
    **old.PINS,
    ACCEPTED: '748e13d9613d94a2017d12588bd5233e315aea7f834acad48e730e7b64bcb76e',
    'verification/browser_twentieth_maker01.py': '98fd60920a6f67ed3560debaced2324bb5493cf1e5ba52406ace71d00d91241a',
    'browser/01-twentysecond-final.txt': '2c843176707a82304f8d7f9196d945c174ce94f85ffb769f3a4eee02476bb43e',
    'browser/01-twentysecond-final-main.txt': 'b91e3abea73da57d0e651d3088c644f0368431527bef55cd21ee55a655fe39ea',
}
REMOVED = tuple(map(frozenset, (
    ((13,9),(13,11)), ((13,10),(14,10)))))
ADDED = tuple(map(frozenset, (
    ((13,9),(13,10)), ((11,10),(14,10)), ((13,11),(13,12)),
    ((1,12),(2,12)), ((4,12),(5,12)), ((7,12),(8,12)),
    ((10,12),(11,12)), ((12,12),(14,12)),
    ((1,13),(2,13)), ((4,13),(5,13)), ((7,13),(8,13)), ((9,13),(10,13)),
    ((1,14),(2,14)), ((4,14),(5,14)), ((7,14),(8,14)), ((9,14),(10,14)),
    ((11,13),(11,14)), ((12,13),(12,14)), ((13,13),(13,14)), ((14,13),(14,14)),
    ((3,12),(3,13)), ((6,12),(6,13)), ((5,10),(6,14)), ((8,10),(9,12)))))
UNMATCHED = frozenset(((1,1),(4,1),(7,1),(14,1),(14,2),(1,3),(4,3),(8,3),
    (14,3),(8,5),(3,6),(6,6),(1,8),(3,10),(9,10),(3,14)))
# Body direction, fixed coordinate, start, literal hook, unmatched fresh cells.
RESIDUALS = (
    ('C',2,10,((3,13),(3,14)),((3,14),)),
    ('C',7,10,((6,13),(6,14)),()),
    ('C',8,10,((9,13),(9,14)),()),
    ('C',9,10,((8,13),(8,14)),((9,10),)),
    ('C',11,10,((10,13),(10,14)),()),
    ('C',2,11,((3,10),(3,11)),((3,10),)),
    ('C',4,11,((3,10),(3,11)),((3,10),)),
    ('C',5,11,((6,10),(6,11)),()),
    ('C',7,11,((8,10),(8,11)),()),
    ('C',8,11,((7,10),(7,11)),()),
    ('C',8,11,((9,10),(9,11)),((9,10),)),
    ('C',10,11,((9,10),(9,11)),((9,10),)),
    ('C',10,11,((11,10),(11,11)),()),
    ('R',13,10,((9,12),(10,12)),()),
    ('R',13,10,((13,12),(14,12)),()),
)
HISTORY = (((10,13),(9,13)), ((11,13),(11,14)),
           ((12,13),(12,14)), ((13,13),(13,14)), ((13,12),(14,12)))
RELEASED_PAIR = frozenset(((14,9),(14,11)))
NEW_PAIR = frozenset(((13,11),(14,9)))
RELEASED_CELLS = frozenset(((12,12),(14,11)))


def need(ok,message):
    if not ok:raise ValueError(message)


def points(cells):
    return [list(q) for q in sorted(cells)]


def full_target(direction,fixed,start,hook):
    need(direction in ('R','C'),'invalid body direction')
    body=frozenset((start+i,fixed) if direction=='R' else (fixed,start+i) for i in range(4))
    hook=frozenset(hook)
    need(len(body)==4 and len(hook)==2 and not body&hook,'invalid body/hook split')
    return body|hook,body,hook


def context(source,geometry):
    need(source['status']=='verified_partial_regional_pairing_obstruction'
         and source['source_sha256']==PINS['verification/browser_twentieth_maker01.py']
         and source['input_sha256']==old.PINS and source['geometry_count']==1040
         and source['full_physical_defense'] is False,'wrong accepted regional source')
    parent=json.loads((BASE/'verification/browser_fifteenth_maker01.json').read_text())['residuals']['R_gap']
    first=json.loads((BASE/'verification/browser_seventeenth_maker01.json').read_text())['acquisition']['first_stage_open_states']['(5, 3)']
    pm,pb=old.physical(parent['maker']),old.physical(parent['breaker'])
    literal.bind_state(parent,pm,pb,26)
    m,b=old.advance(pm,pb,(6,3),(5,3),geometry,literal.V)
    literal.bind_state(first,m,b,27)
    need(source['parent_state']==parent and source['original_state']==old.state(m,b),
         'old physical colors or exact first reply changed')
    pairs=tuple(old.physical(p) for p in source['pairs'])
    endpoints=literal.pairing(pairs,literal.V-m-b)
    need(len(pairs)==41 and len(endpoints)==82 and endpoints<=old.UPPER,
         'accepted41 upper pairs or their reservation changed')
    return m,b,pairs


def classify(m,b,pairs,geometry,tick):
    need(m|b<=literal.V and not m&b and not any(e<=m for e in geometry),'invalid or already won physical state')
    endpoints=literal.pairing(pairs,literal.V-m-b)
    rows=[];live=set();covered=set()
    for edge,(body,hook) in sorted(geometry.items(),key=lambda item:sorted(item[0])):
        tick();indices=[i for i,p in enumerate(pairs) if p<=edge]
        row=dict(target=points(edge),body=points(body),hook=points(hook),old_maker=points(edge&m),
            breaker_hits=points(edge&b),required_free=points(edge-m-b),pair_indices=indices,
            unmatched_fresh=points(edge-m-b-endpoints))
        rows.append(row)
        if not edge&b:
            live.add(edge)
            if indices:covered.add(edge)
    return rows,live,covered,literal.V-m-b-endpoints


def prepare_matching(source,m,b,original,geometry,tick):
    need(len(REMOVED)==2 and set(REMOVED)<=set(original) and len(ADDED)==24,
         'literal41-minus2-plus24 exchange differs')
    pairs=tuple(p for p in original if p not in REMOVED)+ADDED
    need(len(pairs)==63,'wrong proposed matching size')
    rows,live,covered,unmatched=classify(m,b,pairs,geometry,tick)
    need(unmatched==UNMATCHED and len(unmatched)==16,'exact unmatched fresh inventory differs')
    expected={old.physical(r['target']):r for r in source['classification']['live_targets']}
    old_covered={e for e,row in expected.items() if row['pair_indices']}
    need(live==set(expected) and len(live)==385 and len(old_covered)==253 and old_covered<=covered,
         'upper exchange lost a formerly protected full target')
    for e,row in expected.items():
        need(old.physical(row['old_maker'])==e&m and old.physical(row['missing'])==e-m,
             'accepted target inventory erased old ownership')
    need(len(covered)==370,'proposed full coverage count differs')
    declared={};residual_rows=[]
    mate={q:next(iter(p-{q})) for p in pairs for q in p}
    for index,record in enumerate(RESIDUALS,1):
        tick();edge,body,hook=full_target(*record[:4]);u=frozenset(record[4])
        need(edge in geometry and edge in live-covered and edge&unmatched==u and len(u)<=1,
             'invalid or covered residual witness T'+str(index))
        need(edge not in declared,'repeated residual target')
        need(all(mate[q] not in edge for q in edge-m-u),'a paired residual cell has its mate in the target')
        declared[edge]=index
        residual_rows.append(dict(id='T'+str(index),target=points(edge),body=points(body),hook=points(hook),
            old_maker=points(edge&m),required_free=points(edge-m),unmatched_fresh=points(u),
            paired_requirements=[dict(cell=list(q),mate=list(mate[q])) for q in sorted(edge-m-u)]))
    need(len(declared)==15 and set(declared)==live-covered,'the15-target remainder is not complete')
    need(all(len(e&unmatched)<2 for e in declared),'an additional pair could fit a residual target')
    need(old.WITNESSES['W3'] in covered and old.WITNESSES['W9'] in covered,
         'old anchor witnesses were incorrectly retained as exceptions')
    exchange=[]
    for p in REMOVED:
        incidences=[]
        for edge in sorted((e for e in live if p<=e),key=lambda e:sorted(e)):
            new_indices=[i for i,q in enumerate(pairs) if q<=edge]
            need(new_indices,'removed upper pair exposes a live target')
            incidences.append(dict(target=points(edge),replacement_pair_indices=new_indices))
        exchange.append(dict(removed_pair=points(p),all_live_incidences=incidences))
    return pairs,covered,declared,dict(all_full_targets=rows,live_count=385,protected_count=370,
        old_protected_count=253,old_protected_family_preserved=True,unmatched_fresh=points(unmatched),
        pair_count=63,pairs=[points(p) for p in pairs],removed_pairs=[points(p) for p in REMOVED],
        added_pairs=[points(p) for p in ADDED],upper_exchange_audit=exchange,residuals=residual_rows,
        no_additive_matching_on_unmatched_cells=True,
        additive_scope='Each exception has fewer than two unmatched fresh cells, so no new pair disjoint from all63 fixed pairs can cover even one exception. This does not exclude repartitioning or a history-dependent policy.')


def preserve_protected(covered,m,b,pairs,tick):
    literal.pairing(pairs,literal.V-m-b);rows=[]
    for edge in sorted(covered,key=lambda e:sorted(e)):
        tick();hits=edge&b;indices=[i for i,p in enumerate(pairs) if p<=edge]
        need(hits or indices,'a previously protected full target lost protection: '+str(sorted(edge)))
        rows.append(dict(target=points(edge),breaker_hits=points(hits),fresh_pair_indices=indices))
    return rows


def switch_history(m,b,pairs,covered,declared,geometry,tick,history=HISTORY):
    initial_m,initial_b=m,b;records=[];active=pairs
    for index,(u,v) in enumerate(history):
        tick();need(u in literal.V-m-b and v in literal.V-m-b-{u},'stale history move or reply')
        need(not any(e<=m|{u} for e in geometry),'history continues after an immediate physical Maker win')
        if index<4:
            need(frozenset((u,v)) in active,'first four history replies must be actual listed mates')
        else:
            need(index==4 and u==(13,12) and v==(14,12),'wrong conditional override')
            old_mate=(13,11);terminal=(14,12);target=next(e for e,i in declared.items() if i==15)
            need(frozenset((u,old_mate)) in active and old_mate in literal.V-m-b-{u},'old nominal mate not fresh')
            need(terminal in literal.V-m-b-{u,old_mate} and target<=m|{u,terminal}
                 and not target&(b|{old_mate}),'old fifth mate does not allow the claimed immediate T15 win')
            old_failure=dict(maker=list(u),old_mate=list(old_mate),winning_next_claim=list(terminal),
                full_target=points(target),win_checked_before_any_later_breaker_reply=True)
        m,b=old.advance(m,b,u,v,geometry,literal.V)
        retired=[p for p in active if p&(m|b)]
        active=tuple(p for p in active if not p&(m|b))
        if index==4:
            need(RELEASED_PAIR in active,'released D pair is not still active and fresh')
            active=tuple(p for p in active if p!=RELEASED_PAIR)+(NEW_PAIR,)
        proof=preserve_protected(covered,m,b,active,tick)
        records.append(dict(round=index+1,maker=list(u),breaker=list(v),maker_after=points(m),breaker_after=points(b),
            retired_pairs=[points(p) for p in retired],active_pair_count=len(active),
            previously_protected_targets_checked=len(proof)))
    need(len(history)==5 and initial_m<=m and initial_b<=b and len(m)==len(b)==32,
         'five-round history lost old colors or exact parity')
    need(m==initial_m|{u for u,v in HISTORY} and b==initial_b|{v for u,v in HISTORY},'full actual32+32 colors differ')
    need(len(active)==57 and frozenset(((10,12),(11,12))) in active,'unexpected final retained pair policy')
    full_rows,live,now_covered,unmatched=classify(m,b,active,geometry,tick)
    need(RELEASED_CELLS<=literal.V-m-b and unmatched==UNMATCHED|RELEASED_CELLS,
         'released cells were granted ownership or lost from the free inventory')
    killed=sorted(i for edge,i in declared.items() if edge&b)
    need(killed==[3,4,15] and live-now_covered=={edge for edge,i in declared.items() if i not in killed},
         'exact live12-target exceptional remainder differs')
    preservation=preserve_protected(covered,m,b,active,tick)
    released_audit=[]
    for p in (frozenset(((13,11),(13,12))),RELEASED_PAIR):
        witnesses=[]
        for edge in sorted((e for e in covered if p<=e),key=lambda e:sorted(e)):
            hits=edge&b;indices=[i for i,q in enumerate(active) if q<=edge]
            need(hits or indices,'a nontrivially released pair lost its target protector')
            witnesses.append(dict(target=points(edge),breaker_hits=points(hits),new_pair_indices=indices))
        released_audit.append(dict(released_pair=points(p),all_initial_live_incidences=witnesses))
    return m,b,active,dict(history=records,old_fifth_mate_failure=old_failure,
        released_pair=points(RELEASED_PAIR),new_pair=points(NEW_PAIR),released_cells_still_free=points(RELEASED_CELLS),
        final_state=old.state(m,b),final_pairs=[points(p) for p in active],final_unmatched_fresh=points(unmatched),
        preserved_initial_protected_family=preservation,nontrivial_release_audit=released_audit,
        all_full_targets_after=full_rows,live_targets_after=len(live),protected_live_targets_after=len(now_covered),
        killed_initial_exceptions=['T'+str(i) for i in killed],
        remaining_exceptions=['T'+str(i) for i in range(1,16) if i not in killed],
        exact_history_only=True,all_entry_switch_policy=False,full_physical_defense=False)


def audit(tick):
    for name,expected in PINS.items():
        tick();need(hashlib.sha256((BASE/name).read_bytes()).hexdigest()==expected,'changed input: '+name)
    source=json.loads((BASE/ACCEPTED).read_text());geometry=literal.literal_geometry(tick)
    need(len(geometry)==1040,'wrong full14-board geometry')
    m,b,original=context(source,geometry)
    pairs,covered,declared,classification=prepare_matching(source,m,b,original,geometry,tick)
    after_m,after_b,after_pairs,switch=switch_history(m,b,pairs,covered,declared,geometry,tick)
    controls=[]
    def reject(name,operation):
        try:operation()
        except ValueError as error:controls.append(dict(name=name,rejected=True,reason=str(error)));return
        raise ValueError('negative control accepted: '+name)
    bad=deepcopy(source);bad['original_state']['maker'].remove([3,11])
    reject('dropped_old_Maker_anchor',lambda:context(bad,geometry))
    bad=deepcopy(source);bad['original_state']['breaker'].remove([5,3])
    reject('dropped_actual_B53',lambda:context(bad,geometry))
    reject('overlapping_added_pair',lambda:literal.pairing(pairs+(pairs[0],),literal.V-m-b))
    reject('owned_pair_endpoint',lambda:literal.pairing((frozenset((min(m),min(UNMATCHED))),),literal.V-m-b))
    reject('dropped_full_residual',lambda:need(set(list(declared)[:-1])==set(declared),'incomplete physical remainder'))
    wrong=(((10,13),(9,14)),)+HISTORY[1:]
    reject('wrong_early_mate',lambda:switch_history(m,b,pairs,covered,declared,geometry,tick,wrong))
    reject('missing_new_switch_pair',lambda:preserve_protected(covered,after_m,after_b,
        tuple(p for p in after_pairs if p!=NEW_PAIR),tick))
    reject('retained_D_overlaps_new_pair',lambda:literal.pairing(after_pairs+(RELEASED_PAIR,),literal.V-after_m-after_b))
    reject('false_complete_defense',lambda:need(not declared,'15 live targets remain initially unprotected'))
    return dict(status='verified_63pair_partial_defense_and_conditional_switch',
        parent_state=source['parent_state'],original_state=source['original_state'],original_pairs=source['pairs'],
        geometry_count=1040,classification=classification,pair_invariant=old.pair_rule_check(),
        conditional_switch=switch,negative_controls=controls,full_physical_defense=False,
        all_reply_Maker_win=False,unrestricted_static_impossibility=False,new_game_search=False,
        scope='Exact R_gap+M(6,3)/B(5,3), retaining all27+27 colors:63pairs protect370 of385 live full targets. No additive matching on their unmatched cells covers an exception. The exact five-round override preserves all370 protected targets and leaves12 exceptions; it is not an all-entry policy or a complete conditional defense.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();need(not args.output.exists(),'fresh report path required')
    cpu,wall=time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu>=8 or time.monotonic()-wall>=25:raise TimeoutError('finite63-pair audit cap')
    result=dict(schema='snaky-browser-twentysecond-maker01-v1',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        input_sha256=PINS,created_utc=datetime.now(timezone.utc).isoformat())
    try:result.update(audit(tick))
    except (ValueError,KeyError,TypeError,OSError,StopIteration,TimeoutError) as error:
        result.update(status='UNKNOWN' if isinstance(error,TimeoutError) else 'rejected',reason=str(error))
    result.update(process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall)
    with args.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({k:result.get(k) for k in ('status','reason','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_63pair_partial_defense_and_conditional_switch')


if __name__=='__main__':raise SystemExit(main())
