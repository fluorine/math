#!/usr/bin/env python3
"""Independent finite audit of Browser02's six-cell N30 left restoration.

This proves protection of assigned full targets, not a complete N30 defense.
Only frozen independent geometry/pairing helpers are imported; no constructor,
solver, catalog or minimax search is used. Fixed-policy reachability is finite.
"""
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
    'browser/02-twentythird-final.txt': '585f89dc870f41275695724c39727fe0c3df02d392f4a6c2ee4dfadf115dd783',
    'browser/02-twentythird-final-main.txt': '6d8843084412fdf7a8a979d0506aafde57d6ce1a7cfa76f612eef48b4d343438',
    'browser/02-twentythird-prompt.txt': '13d88da487d748621022d777f6dad89394b945383cca4e42c946c64f5f7f760d',
    'maker/fourteenth-n-repair-prefix.json': 'a3714d593e7a0328e8a205d402aa8c329c0562b95256beb384dcae8092560466',
    'maker/earlier-pairing-row-result.pairing.json': '4798216f6401073a9c8830a7c65d454207268f856840d1fd5cf80732a421e8ea',
    'verification/earlier_pairing_replay.json': 'c228eae5cc77312edba72808500acee0145660a80e83d0cf8877fec78b427fec',
    'verification/n32_reserved_controller.json': '00c41e71a3c4c22a0c2e44b97f9c444bc5963401b39494ec3e62ea2563454f60',
    'verification/n32_reserved_controller.py': '106a5f8441554e68440ba24ff0338c0c22f2c802d1d4b393dd4a6dc0800c12fc',
    'verification/browser_eighteenth_maker.py': '747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
    'verification/descendant_pairing_replay.py': '42b67d5d9c6cac3334c563f6a762e1ff6b8fcaaedaf9e5c0828db1e28f1110eb',
}
POINTS = dict(A0=(4,10),A1=(4,11),U=(2,10),V=(3,10),W=(3,9),Z=(3,11))
L = frozenset(POINTS.values())
OUTSIDE = 'outside_unmatched'


def need(ok,message):
    if not ok: raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest()


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def named(*names):
    return frozenset(POINTS[name] for name in names)


def canonical(family):
    return sorted([list(q) for q in sorted(t)] for t in family)


GUARDS = (named('A0','A1'),named('A0','U','V'),named('W','V','Z'),named('A1','V','Z'))
RELEASED = frozenset((named('U','V'),named('W','Z')))
FIXED = tuple(frozenset(pair) for pair in (
    ((2,8),(2,9)),((2,11),(2,12)),((3,7),(3,8)),((3,12),(3,13)),((4,12),(5,12))))


def policies():
    data = {
        'A0':('A1',(('U','V'),('W','Z'))),
        'A1':('A0',(('V','Z'),)),
        'U':('A0',(('V','Z'),)),
        'V':('A1',(('A0','U'),('W','Z'))),
        'W':('A1',(('A0','U'),('V','Z'))),
        'Z':('A1',(('A0','U'),('W','V'))),
        OUTSIDE:('A1',(('U','V'),('W','Z'))),
    }
    return {key:dict(reply=POINTS[reply],pairs=tuple(named(*p) for p in pairs))
            for key,(reply,pairs) in data.items()}


def physical_witness(vertical,fixed,start,hook):
    body=frozenset((fixed,t) if vertical else (t,fixed) for t in range(start,start+4))
    tail=frozenset(hook)
    return body|tail,(body,tail)


def supplied_exposures():
    uv_specs = (
        (False,10,2,((1,9),(2,9))), (False,10,2,((1,11),(2,11))),
        (True,2,7,((3,10),(3,11))), (True,2,10,((3,9),(3,10))),
        (True,3,7,((2,10),(2,11))), (True,3,10,((2,9),(2,10))))
    revived_specs = (
        (False,11,1,((4,10),(5,10))), (False,11,1,((4,12),(5,12))),
        (True,4,10,((3,9),(3,10))), (True,4,10,((3,13),(3,14))),
        (True,4,10,((5,9),(5,10))), (True,4,10,((5,13),(5,14))),
        (True,4,11,((3,10),(3,11))), (False,12,4,((3,11),(4,11))),
        (True,3,7,((4,10),(4,11))), (True,5,7,((4,10),(4,11))),
        (True,3,11,((4,10),(4,11))), (True,3,8,((4,11),(4,12))))
    return tuple(physical_witness(*r) for r in uv_specs),tuple(physical_witness(*r) for r in revived_specs)


def bind_inputs(literal,replay,geometry,tick):
    prefix=json.loads((BASE/'maker/fourteenth-n-repair-prefix.json').read_text())
    need(prefix['status']=='verified_two_arrow_conditional_reduction' and prefix['geometry_count']==1040,
         'unaccepted original prefix')
    maker=literal.CROSS_M-frozenset(((13,7),(13,8),(13,9),(12,8),(11,8),(4,10),(11,5)))
    breaker=literal.CROSS_B-frozenset(((13,5),(14,7),(14,9),(12,9),(12,7),(4,11),(11,6)))
    literal.bind_state(dict(prefix['parent'],stones_each=30),maker,breaker,30)
    need([(r['maker_move'],r['forced_reply']) for r in prefix['arrows']]
         ==[([4,10],[4,11]),([11,5],[11,6])],'two recorded arrows changed')
    prompt=(BASE/'browser/02-twentythird-prompt.txt').read_text()
    states={}
    for name,m,b,marker,count in (
        ('N30',maker,breaker,'Full N30 state (coordinates1..14 on one fixed board):',30),
        ('N31',maker|named('A0'),breaker|named('A1'),'Full N31 state:',31)):
        need(prompt.count(marker)==1,'ambiguous submitted '+name)
        submitted,_=json.JSONDecoder().raw_decode(prompt.split(marker,1)[1].lstrip())
        literal.bind_state(dict(submitted,stones_each=count),m,b,count)
        states[name]=dict(board=[1,1,14,14],maker=sorted(m),breaker=sorted(b),turn='Maker',stones_each=count)
    n32=json.loads((BASE/'verification/n32_reserved_controller.json').read_text())
    need(n32['status']=='independently_verified_full_conditional_N32_breaker_controller'
         and n32['source_sha256']==PINS['verification/n32_reserved_controller.py'],'unaccepted N32 binding')
    nm=maker|named('A0')|{(11,5)}; nb=breaker|named('A1')|{(11,6)}
    literal.bind_state(dict(prefix['final_state'],stones_each=32),nm,nb,32)
    literal.bind_state(n32['original_state'],nm,nb,32)
    need(not literal.cells(n32['reserved_domain'])&L,'left support overlaps accepted right reserve')
    cert=json.loads((BASE/'maker/earlier-pairing-row-result.pairing.json').read_text())
    row_m=literal.CROSS_M-{(13,8),(13,9)}; row_b=literal.CROSS_B-{(14,7),(14,9)}
    checked=replay.check_certificate(cert,row_m,row_b,geometry,literal,tick)
    accepted=json.loads((BASE/'verification/earlier_pairing_replay.json').read_text())
    need(accepted['status']=='independently_verified_full_conditional_breaker_pairing'
         and accepted['state']==json.loads(json.dumps(checked)) and len(checked['pairs'])==54,
         'accepted full L_row certificate differs')
    original=tuple(replay.physical(p) for p in cert['pairs'])
    marker='Its full pair list P is:'
    need(prompt.count(marker)==1,'ambiguous supplied original matching')
    supplied,_=json.JSONDecoder().raw_decode(prompt.split(marker,1)[1].lstrip())
    need(len(supplied)==54 and frozenset(map(literal.cells,supplied))==frozenset(original),'supplied P differs')
    return maker,breaker,original,states,n32['reserved_domain']


def post_maker(maker,breaker,move,targets):
    need(move is None or move in L-maker-breaker,'local Maker claim is not fresh')
    after=maker if move is None else maker|{move}
    need(not any(t<=after for t in targets),'protected local target completed before a response')
    return after


def local_replay(entry,row,targets,tick):
    """All reached local colors, with exterior moves and committed fillers.

    None is a projection of a real exterior claim, not a physical pass. Adding
    impossible exterior availability overapproximates safety. Every local
    Maker claim, including the last one, is checked before a reply is chosen.
    """
    maker=frozenset() if entry==OUTSIDE else named(entry)
    start=(maker,frozenset({row['reply']})); pending=[start]; seen=set()
    entries=fillers=final=0
    while pending:
        tick();m,b=pending.pop()
        if (m,b) in seen: continue
        seen.add((m,b)); need(len(seen)<=729,'six-cell replay exceeded all colored states')
        for u in (None,*sorted(L-m-b)):
            nm=post_maker(m,b,u,targets); free=L-nm-b
            if u is not None and not free: final+=1
            mates=[next(iter(p-{u})) for p in row['pairs'] if u in p and p-{u}<=free] if u else []
            need(len(mates)<=1,'ambiguous mate response')
            replies=mates if mates else (None,*sorted(free))
            for v in replies:
                nb=b if v is None else b|{v}
                if (nm,nb) not in seen: pending.append((nm,nb))
                if not mates: fillers+=1
            entries+=1
    return dict(states=len(seen),post_Maker_checks=entries,arbitrary_filler_transitions=fillers,
                final_local_Maker_claims=final)


def pair_invariant():
    safe={s for s in product(range(3),repeat=2) if 1 not in s or 2 in s}
    moves=fillers=final=0
    for s in safe:
        for u in (0,1):
            if s[u]: continue
            moved=list(s);moved[u]=1
            need(moved!=[1,1],'pair completed before response');final+=0 not in moved
            if moved[1-u]==0: moved[1-u]=2
            need(tuple(moved) in safe,'mate response breaks invariant')
            filled=list(s);filled[u]=2;need(tuple(filled) in safe,'filler breaks pair invariant')
            moves+=1;fillers+=1
    need(final>0,'no final-claim pair check')
    return dict(safe_colorings=len(safe),Maker_steps=moves,filler_steps=fillers,final_claims=final)


def inspect(maker,breaker,original,exterior,domain,targets,rows,geometry,literal,tick):
    need(domain==L and domain<=literal.V-maker-breaker,'changed or nonpristine full domain')
    need(len(original)==54 and len(exterior)==52 and RELEASED<=set(original)
         and set(exterior)==set(original)-RELEASED,'only UV/WZ may be released')
    literal.pairing(original,literal.V-maker-breaker)
    literal.pairing(exterior,literal.V-maker-breaker-domain)
    need(set(FIXED)<=set(exterior),'a required unchanged F pair is absent')
    need(len(geometry)==1040 and not any(e<=maker for e in geometry),'wrong geometry or prior physical win')
    need(targets and all(2<=len(t)<=6 and t<=domain for t in targets),'invalid protected trace')
    need(set(rows)==set(POINTS)|{OUTSIDE},'missing/extra first-entry or activation row')
    for entry,row in rows.items():
        entered=frozenset() if entry==OUTSIDE else named(entry)
        need(row['reply'] in domain-entered,'stale/exterior response')
        literal.pairing(row['pairs'],domain-entered-{row['reply']})
        need(not any(t<=entered for t in targets),'first Maker claim wins before reply')
        for target in targets:
            need(row['reply'] in target or any(p<=target for p in row['pairs']),
                 'row fails a surviving selected obligation: '+entry)
    need(rows[OUTSIDE]['reply']==POINTS['A1'] and set(rows[OUTSIDE]['pairs'])==RELEASED,
         'unmatched activation must restore UV/WZ by actual BA1')
    live=frozenset(e for e in geometry if not e&breaker)
    uv,revived=supplied_exposures()
    for edge,decomposition in uv+revived:
        need(geometry.get(edge)==decomposition,'supplied full exposure is not the stated literal Snaky')
    need(len(uv)==6 and len({e for e,_ in uv})==6
         and {e for e,_ in uv}=={e for e in live if named('U','V')<=e},'six UV exposures are not exhaustive')
    need(len(revived)==12 and len({e for e,_ in revived})==12
         and {e for e,_ in revived}=={e for e in live if POINTS['A1'] in e},'twelve revived A1 targets differ')
    for e in geometry:
        if named('W','Z')<=e: need(POINTS['V'] in e,'WZ-to-WVZ containment fails')
    for edge,_ in uv+revived:
        need(any(t<=edge for t in targets) or any(p<=edge for p in FIXED),'exposure lacks stated replacement')
    old_covered={e for e in live if any(p<=e for p in original)}
    covered={e for e in live if any(p<=e for p in exterior) or any(t<=e for t in targets)}
    need(old_covered<=covered and {e for e,_ in revived}<=covered,'an old or revived assigned target is lost')
    ledger=[]
    for edge,(body,hook) in sorted(geometry.items(),key=lambda item:sorted(item[0])):
        tick(); hits=edge&breaker
        ledger.append(dict(target=sorted(edge),body=sorted(body),hook=sorted(hook),old_Breaker_hits=sorted(hits),
            old_Maker_cells=sorted(edge&maker),required_free=sorted(edge-maker-breaker),
            original_pair_indices=[i+1 for i,p in enumerate(original) if p<=edge],
            exterior_pair_indices=[i+1 for i,p in enumerate(exterior) if p<=edge],
            protected_trace_indices=[i+1 for i,t in enumerate(targets) if t<=edge],
            classification='old_Breaker_hit' if hits else 'protected_by_interface' if edge in covered else 'UNASSIGNED'))
    first=[]
    for u in sorted(literal.V-maker-breaker):
        tick();nm=maker|{u}
        need(not any(e<=nm for e in covered),'assigned physical target wins before initial response')
        wins=[sorted(e) for e in live if e<=nm]
        if wins:
            first.append(dict(entry=u,action='game_ends_on_unassigned_target',targets=wins));continue
        mate=[next(iter(p-{u})) for p in exterior if u in p]
        if mate:
            v=mate[0]; committed=exterior; remaining=targets; action='exterior_mate_keep_L_pristine'
        else:
            label=next((k for k,q in POINTS.items() if q==u),OUTSIDE);row=rows[label]
            v=row['reply'];committed=exterior+row['pairs'];remaining=();action='commit:'+label
        need(v in literal.V-nm-breaker,'initial prescribed response is not fresh')
        nb=breaker|{v};unblocked=tuple(p for p in committed if not p&nb)
        literal.pairing(unblocked,literal.V-nm-nb)
        for e in covered:
            if e&nb: continue
            need(any(p<=e for p in unblocked) or any(t<=e for t in remaining),'initial action loses assigned target')
        first.append(dict(entry=u,response=v,action=action))
    forced=frozenset(((5,7),(5,8),(5,9),(5,10),(4,10),(4,11)))
    need(forced in geometry and forced-maker==named('A0','A1') and not forced&breaker,'forced left arrow differs')
    need(len(first)==136,'full N30 first-entry enumeration differs')
    return dict(full_target_ledger=ledger,initial_physical_entries=first,live_count=len(live),
        originally_pair_covered=len(old_covered),protected_live_count=len(covered),
        unassigned_targets=canonical(live-covered),UV_exposures=canonical(e for e,_ in uv),
        WZ_live_exposures=canonical(e for e in live if named('W','Z')<=e),
        revived_A1_targets=canonical(e for e,_ in revived),forced_arrow_witness=sorted(forced))


def audit(tick):
    for name,digest in PINS.items(): tick();need(sha(BASE/name)==digest,'changed input: '+name)
    literal=load('left_restoration_geometry',BASE/'verification/browser_eighteenth_maker.py')
    replay=load('left_restoration_pairing',BASE/'verification/descendant_pairing_replay.py')
    geometry=literal.literal_geometry(tick)
    maker,breaker,original,states,right_domain=bind_inputs(literal,replay,geometry,tick)
    exterior=tuple(p for p in original if p not in RELEASED);rows=policies()
    args=dict(maker=maker,breaker=breaker,original=original,exterior=exterior,domain=L,
              targets=GUARDS,rows=rows,geometry=geometry,literal=literal,tick=tick)
    inventory=inspect(**args)
    local={entry:local_replay(entry,row,GUARDS,tick) for entry,row in rows.items()}
    need(sum(r['final_local_Maker_claims'] for r in local.values())>0,'final local claims were not exercised')
    controls=[]
    def reject(label,operation):
        tick()
        try: operation()
        except ValueError: controls.append(label)
        else: raise ValueError('negative control accepted: '+label)
    for color in ('maker','breaker'):
        altered=deepcopy(states['N30']);altered[color].pop()
        reject('lost_old_'+color,lambda a=altered:literal.bind_state(a,maker,breaker,30))
    def changed(**updates): return inspect(**(args|updates))
    reject('support_not_pristine',lambda:changed(domain=L|{min(maker)}))
    reject('exterior_pair_overlap',lambda:changed(exterior=exterior[:-1]+(exterior[0],)))
    reject('missing_unchanged_F5',lambda:changed(exterior=tuple(p for p in exterior if p!=FIXED[4])))
    bad=deepcopy(rows);del bad['Z'];reject('missing_first_entry',lambda:changed(rows=bad))
    bad=deepcopy(rows);bad['A0']['reply']=POINTS['A0'];reject('response_equals_entry',lambda:changed(rows=bad))
    bad=deepcopy(rows);bad['A1']['pairs']=(named('A1','V'),);reject('pair_uses_Maker_entry',lambda:changed(rows=bad))
    bad=deepcopy(rows);bad['A0']['pairs']+=(named('U','W'),);reject('overlapping_local_pairs',lambda:changed(rows=bad))
    bad=deepcopy(rows);bad['A1']['pairs']=();reject('uncovered_selected_trace',lambda:changed(rows=bad))
    bad=deepcopy(rows);bad[OUTSIDE]['reply']=POINTS['A0'];reject('bad_filler_activation',lambda:changed(rows=bad))
    reject('missing_bottom_revival_guard',lambda:changed(targets=GUARDS[:-1]))
    broken=dict(geometry);del broken[supplied_exposures()[1][0][0]]
    reject('dropped_full_physical_target',lambda:changed(geometry=broken))
    reject('Maker_win_before_mate',lambda:local_replay('A1',rows['A1'],(named('V'),),tick))
    reject('winning_final_claim_without_reply',lambda:post_maker(L-named('A0'),frozenset(),POINTS['A0'],(named('A0','V'),)))
    need(post_maker(frozenset(),L-named('A0'),POINTS['A0'],(named('A0','V'),))==named('A0'),
         'safe final claim rejected')
    return dict(status='verified_conditional_N30_left_restoration_interface',geometry_count=len(geometry),
        states=states,original_pairs=canonical(original),released_pairs=canonical(RELEASED),
        unchanged_exterior_pairs=canonical(exterior),required_fixed_pairs=canonical(FIXED),
        full_reserved_domain=sorted(L),accepted_N32_right_domain=right_domain,
        protected_targets=canonical(GUARDS),rows={k:dict(reply=r['reply'],pairs=canonical(r['pairs'])) for k,r in rows.items()},
        inventory=inventory,local_fixed_policy_replay=local,pair_invariant=pair_invariant(),
        negative_controls=controls,positive_final_claim_control=True,
        complete_N30_defense=False,complete_N31_defense=False,empty_board_result=False,Lean_checked=False,
        scope='All assigned live physical targets are protected by the exact six-cell local controller plus the unchanged52 pairs. Unassigned targets remain open; no backward inference from N32.',
        history_contract='Before entry L stays pristine: exterior pair entries receive their free mates; other compatible disjoint components may respond in their own domains. An unmatched filler may activate L only by actual BA1 and commitment to UV/WZ. No arbitrary filler enters uncommitted L. After commitment use required free mates, otherwise a real fresh filler if play has not ended. Earlier touched exterior pairs have permanent Breaker endpoints; no new pair borrows an unknown exterior cell. The finite local quotient permits extra outside moves/fillers only as a safety overapproximation, not as physical passes.',
        targetwise_lifting='Every protected full target contains an unchanged exterior pair or a protected subset of L. Arbitrary exterior ownership cannot remove either obstruction. Pre-response and final Maker claims are checked; a global win on an unassigned target ends play and is never followed by a prescribed reply.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();need(not args.output.exists(),'preserve previous output')
    cpu,wall=time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu>=4 or time.monotonic()-wall>=20: raise TimeoutError('finite restoration audit cap')
    try: result=audit(tick)
    except TimeoutError as error: result=dict(status='incomplete',reason=str(error))
    except (ValueError,KeyError,TypeError,IndexError,OSError) as error: result=dict(status='rejected',reason=str(error))
    result.update(schema='snaky-browser-twentythird-left-restoration-v1',source_sha256=sha(Path(__file__)),
        input_sha256=PINS,cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall,
        utc=datetime.now(timezone.utc).isoformat())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x') as stream: json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps({k:result.get(k) for k in ('status','reason','cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_conditional_N30_left_restoration_interface')


if __name__=='__main__': raise SystemExit(main())
