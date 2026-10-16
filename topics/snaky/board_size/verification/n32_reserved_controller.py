#!/usr/bin/env python3
"""Independently check the proposed 24-cell physical N32 Breaker controller.

All 1,040 literal targets and the complete old colors are retained. Each
waiting phase is checked by a pristine-domain/retained-pair invariant, and
every exit is checked against full targets. No constructor or solver import,
sampled play, assumed N33 outcome, or virtual physical move is used.
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
    'browser/02-twentysecond-final.txt':
        '64ee91082072b2356f7a84336b7408bd4c22b324bec287009a2c2684479f9f57',
    'browser/02-twentysecond-prompt.txt':
        '84697b05e54b610ea66d4da91151c3c25fbdec880e2db5e7eebd2d65d23729c2',
    'maker/fourteenth-n-repair-prefix.json':
        'a3714d593e7a0328e8a205d402aa8c329c0562b95256beb384dcae8092560466',
    'verification/browser_sixteenth_maker02.json':
        'b4a6cddcf00d819dfc43675f7f8e83b0c328ebc9159ecd57a164194d72e6e083',
    'verification/n33_k10_controller.json':
        'a313b81fbb08c72e3ffe7c17552dc336ace699eafa50bf77146c6b0b511fa61f',
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
             g=(14,8), h=(14,9), i=(14,10), j=(12,7), k=(12,8),
             r=(13,5), s=(13,7), m=(11,4), n=(12,4), p=(12,5),
             q=(12,6), t=(14,5), u=(14,6), v=(13,2), w=(13,3),
             z=(13,4), A=(14,2), B=(14,3), C=(14,4))
# A, B and C denote the proposal's alpha, beta and gamma, not stone colors.
K12_NAMES = 'abcdeghijkrs'
D_NAMES = K12_NAMES + 'mnpqtuvwzABC'
OUTSIDE = 'outside_unmatched'
UNMATCHED = frozenset(((14,1),(6,3),(9,3),(9,5),(4,6),(7,10),(6,11),
    (1,12),(2,13),(6,13),(7,13),(1,14),(2,14),(3,14),(6,14),(14,14)))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def named(names):
    return frozenset(CELLS[name] for name in names)


def plus(family, *pairs):
    return tuple(family) + tuple(named(pair) for pair in pairs)


def minus(family, *pairs):
    removed = {named(pair) for pair in pairs}
    need(removed <= set(family), 'removing a pair absent from the supplied family')
    return tuple(pair for pair in family if pair not in removed)


def commit(reply, pairs):
    return dict(reply=CELLS[reply], pairs=pairs)


def enter(reply, phase):
    return dict(reply=CELLS[reply], phase=phase)


def policies(original):
    """Literal transcription; all geometric and execution claims are checked below."""
    q = minus(original, 'be', 'ch', 'gi')
    r = minus(q, 'mn', 'pq', 'tu', 'vz', 'AB')
    q0 = plus(minus(q, 'vz'), 'wz')
    c0 = ('ak','bc','gi','sd')
    table_a = dict(a=('sk','cd','bh','eg'), b=('ak','sd','ch','gi'),
        c=('sb','ak','jd','gi'), d=('sb','jk','ac','gi'),
        e=c0, h=c0, j=c0, g=('sk','cd','ab','hi'), i=('sd','ak','bh','eg'))
    phases = {}
    def save(name, domain, exterior, rows):
        phases[name] = dict(domain=named(domain), exterior=exterior, rows=rows)
    for label, exterior in (('Q',q), ('Q0',q0)):
        rows = {x:commit('k',plus(exterior,'bc','hi')) for x in 'adegj'}
        rows.update(b=commit('k',plus(exterior,'cd','hi')),
                    c=commit('k',plus(exterior,'bd','hi')),
                    h=commit('k',plus(exterior,'bc','gi')),
                    i=commit('k',plus(exterior,'bc','gh')),
                    k=enter('j','K8_'+label))
        rows[OUTSIDE] = commit('k',plus(exterior,'bc','hi'))
        save('Fs_'+label,'abcdeghijk',exterior,rows)
        additions = dict(s=('aj','be','ch','gi'), a=('sj','be','ch','gi'),
            b=('as','ch','gi'), c=('ab','sj','hi'), e=('ab','sj','hi'),
            g=('ab','sj','hi'), h=('as','bc','gi'), j=('as','bc','gi'),
            i=('as','bc','gh'))
        rows = {x:commit('d',plus(exterior,*pairs)) for x,pairs in additions.items()}
        rows['d'] = commit('s',plus(exterior,'ac'))
        rows[OUTSIDE] = commit('d',plus(exterior,'as','bc','gi'))
        save('Fk_'+label,'abcdeghijs',exterior,rows)
        additions = dict(a=('be','ch','gi'), b=('ae','ch','gi'), c=('ab','hi'),
            e=('ab','ch','gi'), g=('ab','hi'), h=('ae','bc','gi'), i=('ae','bc','gh'))
        rows = {x:commit('d',plus(exterior,*pairs)) for x,pairs in additions.items()}
        rows['d'] = commit('b',plus(exterior,'ac','gi'))
        rows[OUTSIDE] = commit('d',plus(exterior,'be','ch','gi'))
        save('K8_'+label,'abcdeghi',exterior,rows)
    rows = {x:commit('r',plus(q0,*pairs)) for x,pairs in table_a.items()}
    rows.update(r=commit('s',plus(q0,'ak','jd','eh')),
                s=enter('r','Fs_Q0'), k=enter('r','Fk_Q0'))
    rows[OUTSIDE] = commit('r',plus(q0,*c0))
    save('guarded',K12_NAMES,q0,rows)
    rows = {x:commit('r',plus(q,*pairs)) for x,pairs in table_a.items()}
    rows.update(r=commit('s',plus(r,'AB','pm','nz','vw','qj','ue','ak')),
        s=enter('r','Fs_Q'), k=enter('r','Fk_Q'),
        p=commit('n',plus(r,'wz','BC','qm','rt','jk','ac','sb','eg')),
        m=commit('n',plus(r,'wz','BC','pq','rt','jk','ac','sb','eg')),
        t=commit('n',plus(r,'wz','BC','pm','jk','ac','sb','eg')),
        q=enter('p','guarded'), n=enter('m','guarded'), u=enter('t','guarded'),
        v=commit('r',plus(q0,*c0)), z=commit('r',plus(minus(q,'vz'),'vw',*c0)),
        w=commit('r',plus(q,*c0)), C=commit('r',plus(q,*c0)),
        A=commit('r',plus(minus(q,'vz','AB'),'wz','BC',*c0)),
        B=commit('r',plus(minus(q,'vz','AB'),'wz','AC',*c0)))
    rows[OUTSIDE] = commit('r',plus(q,*c0))
    save('initial',D_NAMES,r,rows)
    return phases,dict(R=r,Q=q,Q0=q0)


def matching(pairs, maker, breaker, domain, literal):
    """B-hit pairs are retained protection, not asserted to have free endpoints."""
    endpoints = literal.pairing(pairs,literal.V)
    need(not endpoints & domain,'exterior pair meets the pristine reserved domain')
    for pair in pairs:
        need(not pair & maker or bool(pair & breaker),'unblocked pair contains a known Maker stone')
    return endpoints


def waiting_inventory(geometry, maker, breaker, domain, pairs, guard):
    uncovered, inventory = [], []
    for edge in sorted(geometry,key=lambda e:sorted(e)):
        guard()
        if edge & breaker: continue
        hits = [index for index,pair in enumerate(pairs) if pair <= edge]
        trace = edge & domain
        if not hits:
            need(len(trace)>=2,'waiting target has fewer than two pristine cells: '+str(sorted(edge)))
            uncovered.append((edge,trace))
        inventory.append(dict(target=sorted(edge),pair_indices=hits,reserved_trace=sorted(trace)))
    return uncovered,inventory


def transition_pairs(before, after, maker, breaker, previous_domain, literal):
    """Keep unknown exterior histories safe; all unblocked new pairs are local."""
    matching(after,maker,breaker,frozenset(),literal)
    old = set(before)
    for pair in before:
        need(bool(pair & breaker) or pair in after,'lost an unblocked exterior protection')
    for pair in after:
        if not pair & breaker and pair not in old:
            need(pair <= previous_domain-maker-breaker,
                 'new pair uses a cell outside the preceding pristine domain')


def check_controller(phases, maker, breaker, geometry, literal, guard):
    records,visited = [],set()
    def visit(name,m,b,path):
        guard(); spec=phases[name]; domain=spec['domain']; exterior=spec['exterior']
        need(domain and domain <= literal.V-m-b,'phase domain is not pristine')
        need(not any(edge <= m for edge in geometry),'Maker already won at phase entry')
        matching(exterior,m,b,domain,literal)
        names={n for n,p in CELLS.items() if p in domain}
        rows=spec['rows']; need(set(rows)==names|{OUTSIDE},'missing or extra phase entry row')
        uncovered,inventory=waiting_inventory(geometry,m,b,domain,exterior,guard)
        record=dict(path=path,phase=name,known_maker=sorted(m),known_breaker=sorted(b),
            reserved_domain=sorted(domain),exterior_pairs=[sorted(p) for p in exterior],
            live_target_count=len(inventory),without_exterior_pair=len(uncovered),
            minimum_reserved_trace=min((len(t) for _,t in uncovered),default=None),
            unprotected_targets=[dict(target=sorted(e),trace=sorted(t)) for e,t in uncovered],rows=[])
        records.append(record); visited.add(name)
        for entry,row in rows.items():
            guard(); claimed=frozenset() if entry==OUTSIDE else named(entry)
            reply=row['reply']; need(reply in domain-claimed,'response is not fresh and reserved')
            nm,nb=m|claimed,b|{reply}
            need(not any(edge <= nm for edge in geometry),'Maker wins before the table response')
            need(set(row) in ({'reply','pairs'},{'reply','phase'}),'malformed continuation')
            output=dict(entry=None if entry==OUTSIDE else CELLS[entry],reply=reply)
            if 'phase' in row:
                child=phases[row['phase']]
                need(child['domain'] < domain and child['domain'] <= domain-claimed-{reply},
                     'next domain is not strictly smaller and still pristine')
                transition_pairs(exterior,child['exterior'],nm,nb,domain,literal)
                output['next_phase']=row['phase']
                visit(row['phase'],nm,nb,path+'/'+entry)
            else:
                pairs=row['pairs']; transition_pairs(exterior,pairs,nm,nb,domain,literal)
                live=tuple(edge for edge in geometry if not edge & nb)
                for edge in live:
                    need(any(pair <= edge for pair in pairs),
                         'full target uncovered after '+path+'/'+entry+': '+str(sorted(edge)))
                output.update(committed_pairs=[sorted(p) for p in pairs],
                              live_target_count=len(live),pair_count=len(pairs))
            record['rows'].append(output)
    visit('initial',maker,breaker,'initial')
    need(visited==set(phases),'unused or unchecked phase')
    return records


def pair_invariants():
    safe={state for state in product(range(3),repeat=2) if 1 not in state or 2 in state}
    entries=fillers=final=0
    for state in safe:
        for endpoint in (0,1):
            if state[endpoint]: continue
            moved=list(state); moved[endpoint]=1
            need(moved!=[1,1],'Maker finishes a pair before any Breaker response')
            final+=0 not in moved
            if moved[1-endpoint]==0: moved[1-endpoint]=2
            need(tuple(moved) in safe,'mate response loses protection')
            filled=list(state); filled[endpoint]=2
            need(tuple(filled) in safe,'an arbitrary fresh Breaker filler loses protection')
            entries+=1; fillers+=1
    need(final>0,'final-claim case not checked')
    return dict(safe_colorings=len(safe),maker_steps=entries,filler_steps=fillers,
                final_maker_claims_checked_before_response=final,
                waiting_rule='Untouched exterior pair or Breaker-hit pair; unmatched entry commits by a reserved reply.')


def auxiliary_claims(maker,breaker,geometry,families,guard):
    q,r=families['Q'],families['R']; k=named(K12_NAMES)
    h=named('mprt')|{(10,4),(11,5)}
    u=named('mpq')|{(11,2),(11,3),(11,5)}
    need(h in geometry and u in geometry,'H or U is not a literal full Snaky')
    through_r=[e for e in geometry if CELLS['r'] in e and not e & breaker]
    need(len(through_r)==22,'revived r-target inventory differs from 22')
    no_q=[e for e in geometry if not e & (breaker|named('r')) and not any(p<=e for p in q)]
    need(len(no_q)==10,'lower ten-target classification differs')
    cap=plus(r,'wz','BC','jk','ac','sb','eg')
    no_cap={e for e in geometry if not e & (breaker|named('n')) and not any(p<=e for p in cap)}
    need(no_cap=={h,u},'52-pair cap near-cover has other exceptions')
    for edge in geometry:
        guard()
        if named('vz') <= edge: need(CELLS['w'] in edge,'vz replacement containment fails')
        if named('AB') <= edge:
            need(CELLS['C'] in edge or named('wz')<=edge,'AB replacement containment fails')
    m,b=maker,breaker
    for x,y in (('p','q'),('t','u'),('m','n')):
        need(not named(x+y)&(m|b) and named(x+y) in q,'old waiting counterexample is not legal')
        m=m|named(x); need(not any(e<=m for e in geometry),'counterexample won earlier than recorded')
        b=b|named(y)
    need(CELLS['r'] not in m|b and h <= m|named('r') and not h&b,
         'failed original K12 waiting rule has no stated immediate counterexample')
    return dict(H=sorted(h),U=sorted(u),live_targets_containing_r=[sorted(e) for e in through_r],
        ten_targets_after_actual_Br=[dict(target=sorted(e),K12_trace=sorted(e&k)) for e in no_q],
        cap_near_cover_pairs=[sorted(p) for p in cap],cap_exceptions=[sorted(h),sorted(u)],
        original_K12_counterexample=dict(exchanges=[['p','q'],['t','u'],['m','n']],
                                        final_Maker='r',completed_full_target=sorted(h)))


def audit(guard):
    for path,digest in PINS.items():
        guard(); need(sha(BASE/path)==digest,'changed pinned input: '+path)
    literal=load('n32_literal_geometry',BASE/'verification/browser_eighteenth_maker.py')
    replay=load('n32_literal_pairing',BASE/'verification/descendant_pairing_replay.py')
    geometry=literal.literal_geometry(guard)
    maker=literal.CROSS_M-named('sbcka'); breaker=literal.CROSS_B-named('rehdj')
    declared=json.loads((BASE/'maker/fourteenth-n-repair-prefix.json').read_text())['final_state']
    literal.bind_state(dict(declared,stones_each=32),maker,breaker,32)
    prompt=(BASE/'browser/02-twentysecond-prompt.txt').read_text()
    stated=[json.loads(line) for line in prompt.splitlines() if line.startswith('{"board":')]
    need(len(stated)==1,'prompt has no unique full state')
    literal.bind_state(dict(stated[0],stones_each=32),maker,breaker,32)
    n33=json.loads((BASE/'verification/n33_k10_controller.json').read_text())['original_state']
    literal.bind_state(n33,maker|named('s'),breaker|named('r'),33)
    old=json.loads((BASE/'verification/browser_sixteenth_maker02.json').read_text())
    literal.bind_state(old['residuals']['L_row'],maker|named('ska'),breaker|named('rjd'),35)
    cert=json.loads((BASE/'maker/earlier-pairing-row-result.pairing.json').read_text())
    checked=replay.check_certificate(cert,maker|named('ska'),breaker|named('rjd'),geometry,literal,guard)
    need(len(checked['pairs'])==54 and checked['live_target_count']==257,'accepted L_row binding differs')
    original=tuple(replay.physical(pair) for pair in cert['pairs'])
    phases,families=policies(original); domain=named(D_NAMES); exterior=families['R']
    need(len(domain)==24 and len(exterior)==46 and domain<=literal.V-maker-breaker,'wrong initial partition')
    endpoints=literal.pairing(exterior,literal.V-maker-breaker-domain)
    need(literal.V-maker-breaker-domain-endpoints==UNMATCHED,'16-cell unmatched inventory differs')
    need(len(geometry)==1040 and not any(e<=maker for e in geometry),'geometry or initial win differs')
    records=check_controller(phases,maker,breaker,geometry,literal,guard)
    initial=phases['initial']; initial_moves=[]
    for entry in sorted(literal.V-maker-breaker):
        guard(); need(not any(e<=maker|{entry} for e in geometry),'actual initial entry wins')
        if entry in domain:
            name=next(n for n,p in CELLS.items() if p==entry); row=initial['rows'][name]
            reply=row['reply']; action='table:'+name
        else:
            mate=next((next(iter(p-{entry})) for p in exterior if entry in p),None)
            reply=mate if mate is not None else initial['rows'][OUTSIDE]['reply']
            action='exterior_mate_and_wait' if mate is not None else 'exterior_trigger'
        need(reply in literal.V-maker-breaker-{entry},'actual initial reply is not fresh')
        initial_moves.append(dict(maker_entry=entry,breaker_reply=reply,action=action))
    need(len(initial_moves)==132,'initial legal-move count differs')
    aux=auxiliary_claims(maker,breaker,geometry,families,guard)
    controls=[]
    def reject(name,fn):
        guard()
        try: fn()
        except ValueError: controls.append(name)
        else: raise ValueError('negative control accepted: '+name)
    def changed(name,alter):
        bad=deepcopy(phases); alter(bad)
        reject(name,lambda:check_controller(bad,maker,breaker,geometry,literal,guard))
    reject('dropped_old_Maker',lambda:literal.bind_state(dict(declared,stones_each=32),maker-{min(maker)},breaker,32))
    reject('dropped_old_Breaker',lambda:literal.bind_state(dict(declared,stones_each=32),maker,breaker-{min(breaker)},32))
    reject('same_count_changed_old_color',lambda:literal.bind_state(dict(declared,stones_each=32),(maker-{min(maker)})|named('r'),breaker,32))
    changed('missing_initial_row',lambda p:p['initial']['rows'].pop('r'))
    changed('stale_initial_reply',lambda p:p['initial']['rows']['r'].update(reply=CELLS['r']))
    changed('overlapping_exterior_pairs',lambda p:p['initial'].update(exterior=exterior+(exterior[0],)))
    changed('initial_commitment_omits_all_local_protection',lambda p:p['initial']['rows']['r'].update(pairs=exterior))
    changed('unmatched_exterior_commitment_unprotected',lambda p:p['initial']['rows'][OUTSIDE].update(pairs=families['Q']))
    changed('wrong_K8_transition_reply',lambda p:p['Fs_Q']['rows']['k'].update(reply=CELLS['a']))
    changed('missing_guarded_entry',lambda p:p['guarded']['rows'].pop('r'))
    changed('guarded_r_commitment_unprotected',lambda p:p['guarded']['rows']['r'].update(pairs=families['Q0']))
    changed('Fk_pair_contains_actual_entry',lambda p:p['Fk_Q']['rows']['d'].update(pairs=plus(families['Q'],'ad')))
    changed('missing_K8_outside_trigger',lambda p:p['K8_Q0']['rows'].pop(OUTSIDE))
    changed('lost_previous_exterior_pair',lambda p:p['initial']['rows']['r'].update(pairs=p['initial']['rows']['r']['pairs'][1:]))
    reject('missing_actual_guard',lambda:matching(families['Q0'],maker|named('q'),breaker,named(K12_NAMES),literal))
    reject('new_pair_outside_pristine_domain',lambda:transition_pairs((),(named('vw'),),maker,breaker,named('ab'),literal))
    reject('one_cell_waiting_requirement',lambda:waiting_inventory((named('a'),),frozenset(),frozenset(),named('ab'),(),guard))
    reject('empty_waiting_requirement',lambda:waiting_inventory((frozenset(),),frozenset(),frozenset(),domain,(),guard))
    reject('original_K12_waiting_rule',lambda:waiting_inventory(geometry,maker,breaker,named(K12_NAMES),families['Q'],guard))
    pair_checks=pair_invariants(); guard()
    return dict(status='independently_verified_full_conditional_N32_breaker_controller',complete_defense=True,
        original_state=dict(declared,stones_each=32,status='conditional_Breaker_defense'),
        geometry_count=len(geometry),live_target_count=records[0]['live_target_count'],
        initial_free_count=len(initial_moves),reserved_names=CELLS,reserved_domain=sorted(domain),
        original_pair_count=54,exterior_pairs=[sorted(p) for p in exterior],unmatched_exterior=sorted(UNMATCHED),
        initial_entry_table=initial_moves,phase_contexts=records,
        phase_context_count=len(records),transition_count=sum(len(r['rows']) for r in records),
        commitment_count=sum('committed_pairs' in row for r in records for row in r['rows']),
        auxiliary_literal_checks=aux,pair_color_invariants=pair_checks,negative_controls=controls,
        response_rule='While a phase domain is pristine, take a fresh exterior mate when required and keep waiting. '
            'A first reserved entry or unmatched exterior move uses its actual reserved reply and listed continuation. '
            'After a matching commitment take a fresh mate if required, otherwise the lexicographically least fresh '
            'physical cell (x, then y), if any. No waiting-phase filler, pass, or virtual physical claim is used.',
        proof_contract='All live targets have an exterior pair or at least two pristine reserved cells. '
            'Every transition retains old unblocked pair protection and installs new unblocked pairs only inside the '
            'previous pristine domain; child domains strictly shrink. Every commitment covers all full live targets. '
            'The pair invariant prevents completion on every Maker claim, including the final legal claim.',
        scope='Complete physical Breaker defense only at the exact Maker-to-move N32 32+32 state. '
            'No earlier-state loss, empty-board result, board-size bound, or novelty claim follows.')


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(); need(not args.output.exists(),'fresh report required')
    wall,cpu=time.monotonic(),time.process_time()
    def guard():
        if time.process_time()-cpu>=8 or time.monotonic()-wall>=25:
            raise TimeoutError('finite N32 controller cap')
    try: result=audit(guard)
    except TimeoutError as error: result=dict(status='incomplete',complete_defense=False,reason=str(error))
    except (ValueError,KeyError,TypeError) as error: result=dict(status='rejected',complete_defense=False,reason=str(error))
    result.update(schema='snaky-independent-n32-reserved-controller-v1',source_sha256=sha(Path(__file__)),
        input_sha256=PINS,utc=datetime.now(timezone.utc).isoformat(),cpu_seconds=time.process_time()-cpu,
        elapsed_seconds=time.monotonic()-wall,limits=dict(cpu_seconds=8,wall_seconds=25))
    with args.output.open('x') as stream: json.dump(result,stream,indent=2,sort_keys=True); stream.write('\n')
    print(json.dumps({k:result.get(k) for k in ('status','complete_defense','live_target_count',
        'phase_context_count','commitment_count','cpu_seconds','elapsed_seconds')}))
    return int(not result['complete_defense'])


if __name__=='__main__':
    raise SystemExit(main())
