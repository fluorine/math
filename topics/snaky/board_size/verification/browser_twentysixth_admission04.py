#!/usr/bin/env python3
"""Finite audit of 35 physical A52 admission rows and their waiting contract.

Only frozen independent geometry/matching/right-table helpers are reused.
Seven first entries into the reserved 42-cell domain remain unresolved.
No solver, policy search, or assumed pass/filler is used.
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
from original_p52_defense import Q, FILL, M as P52_M, B as P52_B

BASE=Path(__file__).resolve().parents[1]
PINS={
    'browser/04-twentysixth-final.txt':'80aabe4174c1accbedc57e9ea9f4dd9a7ad16c1680168c774040d26e9386310a',
    'browser/04-twentysixth-final-main.txt':'61b1ff50ebbc0cc2efe4271e2a811edc68a786cfdd66c4311113dca33a3b2288',
    'browser/04-twentysixth-prompt.txt':'d043b614a820753de45b094a9a755f15f03c2ffaf6076ca2ec29e8c03207b64e',
    'verification/continued_endpoint_defenses.py':'cee9f08d63d4a0e8a28c18967da1917504d2e975a95b7310aa43cdf1c26ed187',
    'verification/original_p52_defense.py':'dc4881010c5150a9dff2421fc5a9899cef183f2d1e866ebfb5e14b6f922a93d1',
    'verification/original-p52-defense-01.json':'51d0885027969cbe0fafdeae9b009c187ad6438c7a6b84fbcf6d38ab1a9c4df1',
}
V=frozenset(range(100))
M=P52_M-{32}; B=P52_B-{33}
S=frozenset((0,1,2,5,6,7,8,9,19,29,32,35,39,48,49,59,60,62,69,72,
             79,80,81,87,88,89,90,91,92,93,95,96,97,98,99))
K=frozenset((13,14,23,24,33,53,54)); D=S|K
WAIT=((3,4),(10,20),(11,21),(12,22),(15,25),(30,40),(31,42),(41,50),
      (51,61),(63,73),(64,65),(66,76),(68,78),(70,71),(82,83),(85,86))
REVIVED=tuple(map(frozenset,((2,12,13,23,33,43),(2,12,22,32,33,43),
    (3,13,23,32,33,42),(4,13,14,23,33,43),(12,22,23,33,43,53),
    (13,23,33,43,44,54),(14,23,24,33,43,53),(22,32,33,43,53,63),
    (23,24,25,26,32,33),(23,24,30,31,32,33),(23,33,43,53,54,64),
    (30,31,32,33,43,44),(32,33,43,44,45,46),(33,43,53,62,63,72))))
TC=frozenset((32,33,43,44,45,46))
TS=frozenset((44,45,46,47,53,54))
TSTAR=frozenset((13,23,33,43,44,54))


def need(ok,why):
    if not ok:
        raise ValueError(why)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def state(m,b):
    return dict(maker=sorted(m),breaker=sorted(b),turn='Maker')


def bind(s):
    need(s==state(P52_M,P52_B),'wrong accepted original P52 colors')
    need(M==frozenset((37,43,44,45,46,47,57,67,75,84)) and
         B==frozenset((34,36,38,52,55,56,58,74,77,94)), 'wrong restored A52 colors')
    need(not M&B and len(M)==len(B)==10 and {32,33} <= V-M-B,'bad restoration')


def declared_rows():
    """Transcribe the final response's local replacements; no optimization."""
    original=set(map(frozenset,Q+FILL)); rows={32:original.copy()}
    def edit(u,remove,add):
        removed=set(map(frozenset,remove)); added=set(map(frozenset,add))
        need(u not in rows and removed <= original,'duplicate row or absent removed pair')
        rows[u]=(original-removed)|added
    for a,b in FILL:
        edit(a,((a,b),),((32,b),)); edit(b,((a,b),),((32,a),))
    edit(5,((5,6),(7,8)),((6,7),(8,32)))
    edit(6,((5,6),(7,8),(2,9)),((5,7),(8,9),(2,32)))
    edit(7,((7,8),(2,9)),((8,9),(2,32)))
    edit(8,((5,6),(7,8)),((6,7),(5,32)))
    for a,b in ((29,49),(59,79),(60,80),(62,72),(81,91),(88,89),(92,93),(95,96)):
        for u,y in ((a,b),(b,a)):
            if a==29:
                remove,add=((a,b),(39,48)),((y,39),(32,48))
            elif a==59:
                remove,add=((a,b),(69,87)),((y,69),(32,87))
            elif a==60:
                remove,add=((a,b),),((y,32),)
            elif a==62:
                remove,add=((a,b),(92,93),(90,97)),((y,92),(90,93),(32,97))
            elif a==81:
                remove,add=((a,b),(60,80)),((y,60),(32,80))
            elif a==88:
                remove,add=((a,b),(69,87)),((y,87),(32,69))
            elif a==92:
                remove,add=((a,b),(90,97)),((y,90),(32,97))
            else:
                remove,add=((a,b),(90,97)),((y,97),(32,90))
            edit(u,remove,add)
    return {u:tuple(sorted((tuple(sorted(p)) for p in pairs))) for u,pairs in rows.items()}


def right_histories():
    """All ordinary right-controller turn boundaries, including exhaustion."""
    local_table(ROWS)
    history=[(frozenset(),frozenset(),None)]
    for u,(v,raw) in ROWS.items():
        for choices in product(range(3),repeat=2):
            hm,hb={u},{v}
            for pair,c in zip(raw,choices):
                if c:
                    hm.add(pair[c-1]); hb.add(pair[2-c])
            history.append((frozenset(hm),frozenset(hb),tuple(map(frozenset,raw))))
    checks=final=0
    for hm,hb,pairs in history:
        need(not hm&hb and len(hm)==len(hb),'unbalanced right history')
        for g in GAMMA:
            need(not g <= hm,'right guard completed at turn boundary')
            if pairs is not None and not g&hb:
                need(any(p <= g and not p&(hm|hb) for p in pairs),'right guard lacks fresh pair')
        for u in R-hm-hb:
            need(not any(g <= hm|{u} for g in GAMMA),'right entry wins before response')
            if pairs is None:
                v,raw=ROWS[u]; after=tuple(map(frozenset,raw))
            else:
                p=next(p for p in pairs if u in p)
                v=next(iter(p-{u})); after=pairs
            need(v in R-hm-hb-{u},'right mate not fresh')
            for g in GAMMA:
                need(v in g or bool(g&hb) or
                     any(p <= g and not p&(hm|hb|{u,v}) for p in after),
                     'right response loses a guard')
            checks+=1; final+=int(len(R-hm-hb)==2)
    need(len(history)==55,'wrong right history quotient')
    return dict(turn_boundaries=len(history),post_Maker_checks=checks,final_Maker_checks=final,
                rows={str(u):dict(reply=v,pairs=raw) for u,(v,raw) in ROWS.items()},
                histories=[dict(maker=sorted(m),breaker=sorted(b),
                    remaining_pairs=[] if p is None else [sorted(q) for q in p if not q&(m|b)])
                    for m,b,p in history])


def audit_rows(edges,rows,tick):
    need(set(rows)==S and len(S)==35 and len(K)==7 and not S&K,'wrong admission domain')
    free=V-M-B; wait=matching(WAIT,free-D-R,free-D-R)
    need(len(wait)==16 and len(D)==42 and len(free)==80 and not D&R,
         'wrong waiting partition')
    original=matching(Q+FILL,V-P52_M-P52_B-R,V-P52_M-P52_B-R)
    need(set(wait) <= set(original),'waiting pair is absent from original certificate')
    need(all(p <= D or p in wait for p in original),'old pair crosses waiting/core boundary')
    live=tuple(e for e in edges if not e&B)
    oldlive=tuple(e for e in edges if not e&P52_B)
    revived=set(live)-set(oldlive)
    need(len(live)==160 and len(oldlive)==146 and revived==set(REVIVED),'wrong exact revived family')
    naive=tuple(map(frozenset,Q+((32,33),)))
    missing=[e for e in live if not any(p <= e for p in naive) and not any(g <= e for g in GAMMA)]
    need(set(missing)=={REVIVED[0],REVIVED[5]},'wrong naive-restoration exceptions')
    # Waiting safety before the first D entry: each old live target has an
    # untouched D pair, a retained waiting pair, or a protected right guard.
    # Each revived target still requires the fresh unentered D cell33.
    waiting=[]
    for e in oldlive:
        ps=[p for p in original if p <= e]; gs=[g for g in GAMMA if g <= e]
        need(ps or gs,'old target has no waiting protector')
        waiting.append(dict(target=sorted(e),D_pairs=[sorted(p) for p in ps if p <= D],
                            waiting_pairs=[sorted(p) for p in ps if p in wait],right_guards=[sorted(g) for g in gs]))
    need(all(33 in e for e in revived) and 33 in D-S,'revived target can advance while waiting')
    results=[]
    for u in sorted(S):
        tick(); m,b=M|{u},B|{33}
        need(u in free-{33} and not any(e <= m for e in live),'admission entry is stale or wins')
        pairs=matching(rows[u],V-m-b-R,V-m-b-R)
        need(len(pairs)==36 and set(wait) <= set(pairs),'row loses a waiting pair')
        need(all(p in wait or p <= D-{u,33} for p in pairs),'new pair crosses reserved domains')
        changed=set(original)^set(pairs)
        need(all(p <= S for p in changed),'row changes an exterior or unresolved cell')
        ledger=[]
        for e in oldlive:
            ps=[p for p in pairs if p <= e]; gs=[g for g in GAMMA if g <= e]
            need(ps or gs,'unprotected full target in admission '+str(u)+': '+str(sorted(e)))
            ledger.append(dict(target=sorted(e),fresh_D_pairs=[sorted(p) for p in ps if p <= D],
                               retained_waiting_pairs=[sorted(p) for p in ps if p in wait],
                               right_guards=[sorted(g) for g in gs]))
        # All six pristine right entries commit a total ordinary matching.
        switches=[]
        for r,(v,raw) in ROWS.items():
            need(not any(e <= m|{r} for e in oldlive),'right entry wins before response')
            total=matching(rows[u]+raw,V-m-b-{r,v},V-m-b-{r,v})
            need(all(e&(b|{v}) or any(p <= e for p in total) for e in edges),
                 'right switch does not cover every surviving physical target')
            switches.append(dict(maker=r,reply=v,pairs=len(total),
                                  live_targets=sum(not e&(b|{v}) for e in edges)))
        released=[]
        for p in set(original)-set(pairs):
            released.append(dict(pair=sorted(p),full_live_incidences=[sorted(e) for e in oldlive if p <= e]))
        results.append(dict(first_maker=u,reply=33,state=state(m,b),outside_pairs=rows[u],
                            full_target_ledger=ledger,released_pair_incidences=released,right_switches=switches))
    return dict(state=state(M,B),fresh_cells=80,live_targets=160,old_live_targets=146,
        revived_targets=[sorted(e) for e in REVIVED],naive_uncovered=[sorted(e) for e in missing],
        admission_entries=sorted(S),unresolved_entries=sorted(K),reserved_domain=sorted(D),
        waiting_pairs=WAIT,right_domain=sorted(R),waiting_old_target_ledger=waiting,
        rows=results,history_contract={
            'waiting_pairs_unchanged_in_every_row':True,'all_changes_inside_admission_domain':True,
            'revived_targets_uncompleted_until_entry_because_33_stays_fresh':True,
            'allowed_waiting_history':'Any mate exchanges in the 16 waiting pairs and the total right controller, in any interleaving.',
            'arbitrary_unlisted_fillers_allowed':False,
            'lifting':'Consumed waiting pairs contain Breaker; untouched ones remain fresh. D is pristine before its first entry. The independent right history quotient preserves each right guard. Every row protector is one of these three disjoint types; no history colors are reset.',
            'exhaustion':'Waiting never needs a filler: 32 outside cells are perfectly paired and R has six cells. D still has42 cells before entry. After admission, each remaining domain has an even number of fresh cells and a total mate/switch policy.'})


def forced_replies(edges,tick):
    need({TC,TS,TSTAR} <= set(edges),'nonliteral forcing witness')
    need((TC|TS|TSTAR)-M <= D and not (TC|TS|TSTAR)&B,'forcing witness depends on waiting cells')
    rows=[]
    # These two trees quantify every actual Breaker reply, including outside D.
    for u,other in ((13,23),(23,13)):
        m=M|{u}; legal=V-m-B; necessary={other,32,33,53,54}
        need(len(legal)==79 and necessary <= legal,'wrong first reply inventory')
        n=wchecks=zchecks=0
        for v in sorted(legal-necessary):
            tick(); n+=1; bm,bb=m|{33},B|{v}
            need(33 not in m|B|{v} and TC-bm=={32} and not TC&bb,'missing physical Tc force')
            for w in V-bm-bb:
                wchecks+=1
                if w!=32:
                    need(32 not in bm|bb|{w} and TC <= bm|{32},'off-line reply survives Tc')
                    continue
                cm,cb=bm|{54},bb|{32}
                need(54 not in bm|bb|{32} and TS-cm=={53} and TSTAR-cm=={other}
                     and not (TS|TSTAR)&cb,'physical fork lost')
                for z in V-cm-cb:
                    pivot,e=(53,TS) if z==other else (other,TSTAR)
                    need(pivot not in cm|cb|{z} and e <= cm|{pivot},'fork final claim fails')
                    zchecks+=1
        rows.append(dict(first_maker=u,necessary_replies=sorted(necessary),
                         excluded_replies=n,forced_reply_checks=wchecks,final_fork_reply_checks=zchecks))
    for u,v,e in ((33,32,TC),(53,54,TS),(54,53,TS)):
        m=M|{u}; legal=V-m-B
        need(e-m=={v} and not e&B and v in legal,'wrong immediate forcing edge')
        for w in legal-{v}:
            need(v not in m|B|{w} and e <= m|{v},'bad reply survives immediate full win')
        rows.append(dict(first_maker=u,necessary_replies=[v],excluded_replies=len(legal)-1,
                         full_target=sorted(e)))
    m,b=M|{33,13},B|{32}; legal=V-m-b; necessary={23,53,54}; checks=0
    need(len(legal)==77 and necessary <= legal,'wrong later reply inventory')
    for v in legal-necessary:
        tick(); cm,cb=m|{54},b|{v}
        need(54 not in m|b|{v} and TS-cm=={53} and TSTAR-cm=={23} and not (TS|TSTAR)&cb,
             'later physical fork lost')
        for z in V-cm-cb:
            pivot,e=(53,TS) if z==23 else (23,TSTAR)
            need(pivot not in cm|cb|{z} and e <= cm|{pivot},'later final Maker claim fails')
            checks+=1
    return dict(full_witnesses=[sorted(TC),sorted(TS),sorted(TSTAR)],first_entries=rows,
        after_M33_B32_M13=dict(necessary_replies=sorted(necessary),excluded_replies=len(legal-necessary),
                              final_fork_reply_checks=checks),
        no_restriction_proved_for=[14,24],
        waiting_history_lifting='All required fresh cells belong to pristine D; prior allowed waiting ownership is outside D and cannot hit a witness or occupy a prescribed pivot. Available outside reply classes are included in the pristine full-board enumeration.',
        full_A52_winner_proved=False)


def controls(edges,rows):
    names=[]
    def reject(name,fn):
        try:
            fn()
        except ValueError:
            names.append(name)
        else:
            raise ValueError('control accepted '+name)
    for color in ('maker','breaker'):
        changed=state(P52_M,P52_B); changed[color].pop()
        reject('lost_old_'+color,lambda:bind(changed))
    reject('restored_cells_treated_occupied',lambda:matching(((32,33),),V-P52_M-P52_B))
    reject('missing_admission_row',lambda:need(set(rows)-{32}==S,'missing32 row'))
    reject('occupied_admission_pair',lambda:matching(((5,32),),V-M-B-{5,33}-R))
    reject('missing_row_mate',lambda:matching(rows[32][:-1],V-M-B-{32,33}-R,V-M-B-{32,33}-R))
    reject('row_pair_overlap',lambda:matching(rows[32]+(rows[32][0],),V-M-B-{32,33}-R))
    reject('waiting_intrudes_core',lambda:matching(WAIT+((13,14),),V-M-B-D-R))
    reject('lost_right_entry',lambda:local_table({u:v for u,v in ROWS.items() if u!=16}))
    reject('omitted_revived_target',lambda:need(set(REVIVED[:-1])=={e for e in edges if not e&B and 33 in e},
                                               'missing revived target'))
    reject('wrong_forcing_reply',lambda:need(TC-(M|{33})=={31},'actual unique completion is32'))
    reject('projection_as_physical_target',lambda:need((TSTAR-M) in edges,'partial guard is not full Snaky'))
    need(TC in edges and TC <= M|{33,32},'positive final Maker claim control')
    return dict(rejections=names,positive_final_claim_controls=1)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    need(not args.output.exists(),'fresh output required')
    cpu,wall=time.process_time(),time.monotonic()
    def tick():
        if time.process_time()-cpu>=4 or time.monotonic()-wall>=25:
            raise TimeoutError('finite admission audit cap')
    result=dict(schema='snaky-browser26-A52-admission-v1',status='pending',checker_sha256=sha(__file__),
                input_sha256=PINS,complete_A52_defense=False,empty_board_result=False,search_performed=False)
    try:
        for p,h in PINS.items():
            need(sha(BASE/p)==h,'changed input '+p)
        accepted=json.loads((BASE/'verification/original-p52-defense-01.json').read_text())
        need(accepted['status']=='verified_complete_original_P52_defense','wrong accepted P52 report')
        bind(accepted['defense']['state'])
        edges=literal_targets(); rows=declared_rows()
        result['admission']=audit_rows(edges,rows,tick)
        result['right_history_quotient']=right_histories()
        result['physical_necessary_replies']=forced_replies(edges,tick)
        result['controls']=controls(edges,rows)
        result.update(status='verified_35_complete_admissions_and_seven_entry_waiting_interface',literal_targets=432)
    except (ValueError,KeyError,TypeError,OSError,TimeoutError,StopIteration) as error:
        result.update(status='incomplete' if isinstance(error,TimeoutError) else 'rejected',reason=str(error))
    result.update(process_cpu_seconds=time.process_time()-cpu,elapsed_seconds=time.monotonic()-wall,
                  created_utc=datetime.now(timezone.utc).isoformat())
    with args.output.open('x') as f:
        json.dump(result,f,sort_keys=True,indent=2); f.write('\n')
    print(json.dumps({k:result[k] for k in ('status','process_cpu_seconds','elapsed_seconds')}))
    return int(result['status']!='verified_35_complete_admissions_and_seven_entry_waiting_interface')


if __name__=='__main__':
    raise SystemExit(main())
