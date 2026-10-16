#!/usr/bin/env python3
"""Independent literal audit of the 41-pair regional R_gap obstruction.

The browser's two JSON blocks are data only. Full physical geometry comes
from the pinned independent body/hook generator, with no search imports.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
BROWSER = 'browser/01-twentieth-final-section.txt'
PINS = {
    BROWSER: '0bf3ab011fb8d4975a0416c09b30c365d992f887d923ba135d5aca8d1de0653e',
    'verification/browser_fifteenth_maker01.json':
        'e89460725766129f91e33b9a5c0688ab33801668e173a3253df23da7117f80b6',
    'verification/browser_seventeenth_maker01.json':
        '22fe6eb28935293196efbb2d1dbd84a4d49709800f8f2983c831c8831689ecc0',
    'verification/browser_eighteenth_maker.py':
        '747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
}
BOTTOM = frozenset((x,y) for x in range(1,15) for y in range(12,15))
UPPER = frozenset((x,y) for x in range(1,15) for y in range(1,12))
FIRST_M, FIRST_B = (6,3),(5,3)
NEXT_M, NEXT_B = (8,2),(9,2)
UNPAIRED = {1:(1,4,7,14),2:(14,),3:(1,4,8,14),5:(8,),6:(3,6),8:(1,),10:(3,5,8,9,11)}
WITNESSES = {
    'W3': frozenset({(2,10),(2,11),(3,11),(3,12),(3,13),(3,14)}),
    'W9': frozenset({(8,10),(8,11),(9,11),(9,12),(9,13),(9,14)}),
    'WR': frozenset({(12,10),(12,11),(12,12),(12,13),(13,9),(13,10)}),
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def physical(raw):
    need(isinstance(raw,list) and all(isinstance(q,list) and len(q)==2
         and all(type(v) is int and 1<=v<=14 for v in q) for q in raw), 'nonliteral physical cells')
    points = frozenset(map(tuple,raw))
    need(len(points)==len(raw), 'repeated physical cell')
    return points


def state(maker,breaker):
    return dict(board=[1,1,14,14],turn='Maker',status='OPEN',stones_each=len(maker),
                maker=[list(q) for q in sorted(maker)],breaker=[list(q) for q in sorted(breaker)])


def advance(maker,breaker,move,reply,geometry,universe):
    need(move in universe-maker-breaker and reply in universe-maker-breaker-{move},
         'stale actual claim/reply')
    need(not any(edge <= maker|{move} for edge in geometry), 'Maker wins before proposed reply')
    return maker|{move},breaker|{reply}


def classify(maker,breaker,pairs,geometry,literal,guard):
    need(not maker&breaker and maker|breaker<=literal.V, 'overlap or out-of-board colors')
    need(not any(edge<=maker for edge in geometry), 'Maker initially owns a winning target')
    literal.pairing(pairs,literal.V-maker-breaker)
    live,covered,uncovered = [],[],[]
    for edge,(body,hook) in sorted(geometry.items(),key=lambda item:sorted(item[0])):
        guard()
        if edge&breaker:
            continue
        indices = [i+1 for i,pair in enumerate(pairs) if pair<=edge]
        row = dict(target=sorted(edge),body=sorted(body),hook=sorted(hook),pair_indices=indices,
                   old_maker=sorted(edge&maker),missing=sorted(edge-maker),bottom_trace=sorted(edge&BOTTOM))
        live.append(row)
        (covered if indices else uncovered).append(row)
    need(live and uncovered, 'expected a genuinely partial regional cover')
    need(all(len(row['bottom_trace'])>=2 for row in uncovered),
         'live target with at most one bottom cell is not protected')
    return dict(live_target_count=len(live),covered_target_count=len(covered),uncovered_target_count=len(uncovered),
        regional_target_count=sum(len(row['bottom_trace'])<=1 for row in live),
        upper_target_count=sum(not row['bottom_trace'] for row in live),
        minimum_uncovered_bottom_trace=min(len(row['bottom_trace']) for row in uncovered),
        live_by_bottom_trace_size=dict(Counter(len(row['bottom_trace']) for row in live)),
        uncovered_by_bottom_trace_size=dict(Counter(len(row['bottom_trace']) for row in uncovered)),
        live_targets=live,uncovered_targets=uncovered)


def witness_checks(maker,breaker,pairs,geometry):
    expected_old = {'W3':{(3,11)},'W9':{(9,11)},'WR':set()}
    result = {}
    for name,edge in WITNESSES.items():
        need(edge in geometry and not edge&breaker and not any(pair<=edge for pair in pairs),
             'explicit witness is not a live uncovered full Snaky: '+name)
        need(edge&maker==expected_old[name], 'witness old-Maker ownership differs: '+name)
        need(len(edge&BOTTOM)==(2 if name=='WR' else 3), 'witness bottom-strip trace differs')
        body,hook = geometry[edge]
        result[name] = dict(target=sorted(edge),body=sorted(body),hook=sorted(hook),
                           old_maker=sorted(edge&maker),bottom_trace=sorted(edge&BOTTOM))
    return result


def pair_rule_check():
    safe = {row for row in product(range(3),repeat=2) if 1 not in row or 2 in row}
    claims = fillers = 0
    for row in safe:
        for i in (0,1):
            if row[i]:
                continue
            moved=list(row);moved[i]=1
            need(moved!=[1,1], 'Maker completes a pair before reply')
            if moved[1-i]==0:
                moved[1-i]=2
            need(tuple(moved) in safe, 'mate response breaks invariant')
            filled=list(row);filled[i]=2
            need(tuple(filled) in safe, 'filler breaks invariant')
            claims+=1;fillers+=1
    return dict(colorings=len(safe),maker_claims_checked_before_reply=claims,filler_cases=fillers)


def audit(guard):
    for name,expected in PINS.items():
        guard();need(sha(BASE/name)==expected,'changed input: '+name)
    spec=importlib.util.spec_from_file_location('twentieth01_literal_geometry',BASE/'verification/browser_eighteenth_maker.py')
    literal=importlib.util.module_from_spec(spec);spec.loader.exec_module(literal)
    geometry=literal.literal_geometry(guard)
    need(len(geometry)==1040,'wrong full geometry count')
    accepted_parent=json.loads((BASE/'verification/browser_fifteenth_maker01.json').read_text())['residuals']['R_gap']
    parent_m,parent_b=physical(accepted_parent['maker']),physical(accepted_parent['breaker'])
    literal.bind_state(accepted_parent,parent_m,parent_b,26)
    maker,breaker=advance(parent_m,parent_b,FIRST_M,FIRST_B,geometry,literal.V)
    accepted_first=json.loads((BASE/'verification/browser_seventeenth_maker01.json').read_text())['acquisition']['first_stage_open_states']['(5, 3)']
    literal.bind_state(accepted_first,maker,breaker,27)
    need({(3,11),(9,11)}<=maker and not BOTTOM&(maker|breaker),'anchors or untouched bottom strip differ')
    blocks=(BASE/BROWSER).read_text().split('\nJSON\n')[1:]
    need(len(blocks)==2,'expected exactly the two literal browser JSON blocks')
    raw_pairs,declared_next=(json.JSONDecoder().raw_decode(block.lstrip())[0] for block in blocks)
    need(isinstance(raw_pairs,list),'pair block is not a list')
    pairs=tuple(physical(pair) for pair in raw_pairs)
    need(len(pairs)==41,'wrong displayed pair count')
    endpoints=literal.pairing(pairs,literal.V-maker-breaker)
    need(len(endpoints)==82 and endpoints<=UPPER,'wrong endpoint count or outside endpoint')
    expected_unpaired=frozenset((x,y) for y,xs in UNPAIRED.items() for x in xs)
    need(len(UPPER-maker-breaker)==100 and UPPER-maker-breaker-endpoints==expected_unpaired
         and len(expected_unpaired)==18,'unpaired upper-cell inventory differs')
    before=classify(maker,breaker,pairs,geometry,literal,guard)
    witnesses=witness_checks(maker,breaker,pairs,geometry)
    need(before['minimum_uncovered_bottom_trace']==2,'claimed sharp boundary differs')
    need(pairs[8]=={NEXT_M,NEXT_B},'ninth pair is not the prescribed actual response')
    next_m,next_b=advance(maker,breaker,NEXT_M,NEXT_B,geometry,literal.V)
    literal.bind_state(declared_next,next_m,next_b,28)
    need(declared_next['status']=='OPEN','browser incorrectly labels the next state solved')
    remaining=pairs[:8]+pairs[9:]
    need(len(remaining)==40,'wrong retained pair count')
    after=classify(next_m,next_b,remaining,geometry,literal,guard)
    next_witnesses=witness_checks(next_m,next_b,remaining,geometry)
    after_covered={frozenset(map(tuple,row['target'])) for row in after['live_targets'] if row['pair_indices']}
    need(all(NEXT_B in map(tuple,row['target']) or frozenset(map(tuple,row['target'])) in after_covered
             for row in before['live_targets'] if row['pair_indices']), 'a live formerly protected target lost protection')
    locations=[]
    for row in before['uncovered_targets']:
        body=frozenset(map(tuple,row['body']));xs={x for x,y in body};ys={y for x,y in body}
        location=dict(body=row['body'],orientation='vertical' if len(xs)==1 else 'horizontal',
                      start=min(ys) if len(xs)==1 else min(xs))
        need((len(xs)==1 and min(ys) in (10,11)) or (len(ys)==1 and next(iter(ys)) in (12,13,14)),
             'uncovered body location contradicts the claimed frontier')
        locations.append(location)
    controls=[]
    def reject(label,operation):
        guard()
        try:operation()
        except ValueError:controls.append(label);return
        raise ValueError('negative control accepted: '+label)
    reject('dropped_old_maker',lambda:literal.bind_state(accepted_first,maker-{min(maker)},breaker,27))
    reject('dropped_old_breaker',lambda:literal.bind_state(accepted_first,maker,breaker-{min(breaker)},27))
    reject('overlapping_pair',lambda:classify(maker,breaker,pairs+(pairs[0],),geometry,literal,guard))
    reject('owned_pair_endpoint',lambda:classify(maker,breaker,(frozenset({min(maker),next(iter(pairs[0]))}),)+pairs[1:],geometry,literal,guard))
    unique=next(row for row in before['live_targets'] if len(row['bottom_trace'])<=1 and len(row['pair_indices'])==1)
    index=unique['pair_indices'][0]-1
    reject('uncovered_regional_target',lambda:classify(maker,breaker,pairs[:index]+pairs[index+1:],geometry,literal,guard))
    reject('stale_next_reply',lambda:advance(maker,breaker,NEXT_M,NEXT_M,geometry,literal.V))
    reject('next_state_loses_old_stone',lambda:literal.bind_state(declared_next,next_m-{min(maker)},next_b,28))
    reject('false_full_defense',lambda:need(before['uncovered_target_count']==0,'full defense is false'))
    guard()
    return dict(schema='snaky-independent-browser-twentieth-maker01-v1',
        status='verified_partial_regional_pairing_obstruction',full_physical_defense=False,
        geometry_count=len(geometry),parent_state=accepted_parent,original_state=state(maker,breaker),
        pairs=[sorted(pair) for pair in pairs],pair_count=len(pairs),upper_free_cells=100,
        upper_unpaired_cells=sorted(expected_unpaired),classification=before,explicit_uncovered_witnesses=witnesses,
        uncovered_body_locations=locations,next_actual_moves=dict(maker=NEXT_M,breaker=NEXT_B),
        next_state=declared_next,next_pairs=[sorted(pair) for pair in remaining],
        next_classification=after,next_uncovered_witnesses=next_witnesses,
        pair_invariant=pair_rule_check(),negative_controls=controls,
        response_rule='After each Maker claim, if the claimed cell has a free listed mate, take it; otherwise take the lexicographically least free physical cell (x then y). Retain every actual filler permanently. If Maker has already won on an uncovered target, the game has ended.',
        proof='Initially all displayed pairs are disjoint and free. Before every later Maker turn, any pair already touched by Maker has a Breaker endpoint. Therefore the next legal Maker claim cannot complete a pair, including the final claim when no further reply may remain. If a fresh mate is required it exists as a legal reply; any other fresh filler preserves the invariant. Every initially blocked target remains blocked. Every initially live target with at most one bottom-strip cell contains a displayed pair, so a win against this fixed policy must use an uncovered target containing at least two bottom-strip cells. All bottom-strip cells were initially free. The three explicit uncovered targets show that this is not a complete target cover and do not themselves give a playable Maker strategy.',
        scope='All-length obstruction to winning targets with at most one cell in rows12–14, at exact R_gap+M(6,3)/B(5,3), and after the explicit M(8,2)/B(9,2) continuation. Both full physical outcomes remain OPEN; no parent outcome or empty-board claim.')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    if args.output.exists():parser.error('fresh output required')
    start,cpu=time.monotonic(),time.process_time()
    def guard():
        if time.process_time()-cpu>=4 or time.monotonic()-start>=20:raise TimeoutError('finite regional audit limit')
    try:result=audit(guard)
    except TimeoutError as error:result=dict(status='incomplete',reason=str(error))
    except (ValueError,KeyError,StopIteration) as error:result=dict(status='rejected',reason=str(error))
    result.update(source_sha256=sha(Path(__file__)),input_sha256=PINS,utc=datetime.now(timezone.utc).isoformat(),
                  cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-start,
                  limits=dict(cpu_seconds=4,wall_seconds=20))
    with args.output.open('x') as stream:json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps({key:result.get(key) for key in ('status','geometry_count','cpu_seconds','elapsed_seconds')},sort_keys=True))
    return int(result['status']!='verified_partial_regional_pairing_obstruction')


if __name__=='__main__':raise SystemExit(main())
