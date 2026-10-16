#!/usr/bin/env python3
"""Emit untrusted Lean literals for accepted N33/N32 finite controllers.

Only source generation: no game search and no imported constructor/checker.
The generated local rows, geometric coverage and semantic composition are
separate kernel proof obligations. Physical coordinates map to 14*(y-1)+x-1.
"""
import hashlib
import json
from pathlib import Path

FORMAL = Path(__file__).resolve().parent
BOARD = FORMAL.parent / 'board_size'
PINS = {
    'verification/n33_k10_controller.json': 'a313b81fbb08c72e3ffe7c17552dc336ace699eafa50bf77146c6b0b511fa61f',
    'verification/n32_reserved_controller.json': '00c41e71a3c4c22a0c2e44b97f9c444bc5963401b39494ec3e62ea2563454f60',
}


def read(path):
    raw = (BOARD/path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PINS[path]
    return json.loads(raw)


def cell(p):
    x, y = p
    assert 1 <= x <= 14 and 1 <= y <= 14
    return 14*(y-1)+x-1


def cells(xs):
    return sorted(map(cell, xs))


def lit(x):
    if isinstance(x, list):
        return '[' + ','.join(map(lit, x)) + ']'
    return str(x)


def write(name, lines):
    p = FORMAL/'Snaky'/f'{name}.lean'
    text = '\n'.join(lines)+'\n'
    if p.exists():
        assert p.read_text() == text, f'refusing changed existing generated {name}'
    else:
        p.write_text(text)


def geometry():
    seed = [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
    result = set()
    for refl in (False, True):
        s = [(x,-y if refl else y) for x,y in seed]
        for _ in range(4):
            mx,my = min(x for x,y in s),min(y for x,y in s)
            o = [(x-mx,y-my) for x,y in s]
            for dx in range(14-max(x for x,y in o)):
                for dy in range(14-max(y for x,y in o)):
                    result.add(tuple(sorted(14*(y+dy)+x+dx for x,y in o)))
            s = [(-y,x) for x,y in s]
    return [set(e) for e in sorted(result)]


EDGES = geometry()


def guards(ctx):
    dom,m,b = set(ctx['domain']),set(ctx['maker']),set(ctx['breaker'])
    assert not dom & (m|b)
    ps = list(map(set, ctx['pairs']))
    gs = {tuple(sorted(e & dom)) for e in EDGES if not e & b and not any(p <= e for p in ps)}
    assert all(len(g) >= 2 for g in gs)
    return [list(g) for g in sorted(gs) if not any(set(h) < set(g) for h in gs)]


def domain_cases(var, domain, h):
    return ['  have cases : ' + ' ∨ '.join(f'{var} = {u}' for u in domain) + ' := by',
            f'    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using {h}',
            '  rcases cases with ' + ' | '.join('rfl' for _ in domain)]


def index_cases(k):
    return [f'  have hiN : i < {k} := List.mem_range.mp hi',
            '  have cases : ' + ' ∨ '.join(f'i = {i}' for i in range(k)) + ' := by omega',
            '  rcases cases with ' + ' | '.join('rfl' for _ in range(k))]


def component_definitions(prefix, pairs, child):
    n = len(pairs)
    lines = [f'private def {prefix}Domains : Nat → List Nat']
    lines += [f'  | {i} => {lit(p)}' for i,p in enumerate(pairs)]
    if child:
        lines += [f'  | {n} => {child}.domain']
    lines += ['  | _ => []', f'private def {prefix}Targets : Nat → List (List Nat)']
    lines += [f'  | {i} => [{lit(p)}]' for i,p in enumerate(pairs)]
    if child:
        lines += [f'  | {n} => {child}.guards']
    lines += ['  | _ => []']
    return lines


def row_proof(u, v, pairs, child):
    k = len(pairs) + bool(child)
    assert k > 0
    pre = f'row{u}'
    dd,tt = pre+'Domains',pre+'Targets'
    m,w = f'[{u}]',f'({v} :: outside 196 domain)'
    lines = component_definitions(pre, pairs, child)
    lines += [f'private theorem {pre}Fresh : Fresh 196 {m} (outside 196 domain) {v} := by',
              '  unfold Fresh', '  decide +kernel',
              f'private theorem {pre}Colors : Disjoint {m} {w} := by',
              '  unfold Disjoint', '  decide +kernel',
              f'private theorem {pre}DomainsFresh : ∀ i ∈ List.range {k}, ∀ x ∈ {dd} i,',
              f'    Fresh 196 {m} {w} x := by', '  unfold Fresh', '  decide +kernel',
              f'private theorem {pre}Disjoint : DomainsDisjoint {k} {dd} := by',
              '  unfold DomainsDisjoint', '  decide +kernel',
              f'private theorem {pre}Shapes : ∀ i ∈ List.range {k}, GuardOK ({dd} i) ({tt} i) := by',
              '  unfold GuardOK', '  decide +kernel',
              f'private theorem {pre}Covers : ProductCovers guards {w} {k} {tt} := by',
              '  unfold ProductCovers', '  decide +kernel',
              f'private theorem {pre}Components : ∀ i ∈ List.range {k},',
              f'    ¬ BlackWins ({tt} i) 196 [] (outside 196 ({dd} i)) := by',
              '  intro i hi'] + index_cases(k)
    for a,b in pairs:
        lines += [f'  · exact pair_component_not_blackWins (N := 196) (a := {a}) (b := {b}) (by decide) (by decide) (by decide)']
    if child:
        lines += [f'  · exact {child}.defense']
    lines += [f'private theorem {pre}Defense : ¬ BlackWins guards 196 {m} {w} := by',
              f'  apply product_not_blackWins {pre}Colors {pre}DomainsFresh {pre}Disjoint',
              f'  · intro i hi g hg; exact ({pre}Shapes i hi g hg).1',
              f'  · intro i hi; exact guard_noComplete_empty ({pre}Shapes i hi)',
              f'  · exact {pre}Components', f'  · exact {pre}Covers', '']
    return lines


def context_source(label, index, ctx, contexts):
    name = f'Breaker{label}Context{index:02}'
    children = sorted({r['child'] for r in ctx['rows'] if 'child' in r})
    lines = ['import Snaky.BreakerRounds']
    lines += [f'import Snaky.Breaker{label}Context{i:02}' for i in children]
    lines += ['', f'namespace Snaky.Breaker{label}.C{index:02}', 'open Snaky.Breaker',
              f'def domain : List Nat := {lit(ctx["domain"])}',
              f'def guards : List (List Nat) := {lit(ctx["guards"])}',
              'theorem shape : GuardOK domain guards := by',
              '  unfold GuardOK', '  decide +kernel', '']
    by_entry = {r['u']: r for r in ctx['rows']}
    assert set(by_entry) == set(ctx['domain'])
    for u in ctx['domain']:
        r = by_entry[u]
        child = f'Snaky.Breaker{label}.C{r["child"]:02}' if 'child' in r else None
        pairs = r['pairs']
        child_ctx = contexts[r['child']] if child else None
        # Early diagnostic only; the generated complete Lean row is decisive.
        used = [x for p in pairs for x in p]
        assert len(used) == len(set(used))
        assert set(used) <= set(ctx['domain']) - {u,r['v']}
        if child:
            assert not set(used) & set(child_ctx['domain'])
            assert set(child_ctx['domain']) <= set(ctx['domain']) - {u,r['v']}
        gs = pairs + (child_ctx['guards'] if child else [])
        for g in ctx['guards']:
            assert r['v'] in g or any(set(h) <= set(g) for h in gs), (label,index,u,g)
        lines += row_proof(u, r['v'], pairs, child)
    lines += ['theorem defense : ¬ BlackWins guards 196 [] (outside 196 domain) := by',
              '  apply local_round_not_blackWins shape', '  intro u hu']
    lines += domain_cases('u', ctx['domain'], 'hu')
    lines += [f'  · exact ⟨{by_entry[u]["v"]}, row{u}Fresh, row{u}Defense⟩' for u in ctx['domain']]
    lines += ['', f'end Snaky.Breaker{label}.C{index:02}']
    write(name, lines)


def whole_source(label, root):
    pairs = root['pairs']
    k = len(pairs)+1
    lines = [f'import Snaky.Breaker{label}Context00', '', f'namespace Snaky.Breaker{label}',
              'open Snaky.Breaker', f'def maker : List Nat := {lit(root["maker"])}',
              f'def breaker : List Nat := {lit(root["breaker"])}']
    lines += component_definitions('root', pairs, 'C00')
    # Public aliases keep the coverage modules simple.
    lines += ['def domains := rootDomains', 'def targets := rootTargets',
              'theorem colors_disjoint : Disjoint maker breaker := by',
              '  unfold Disjoint', '  decide +kernel',
              f'theorem shapes : ∀ i ∈ List.range {k}, GuardOK (domains i) (targets i) := by',
              '  unfold GuardOK', '  decide +kernel']
    for i in range(k):
        lines += [f'private theorem fresh{i} : ∀ x ∈ domains {i}, Fresh 196 maker breaker x := by',
                  '  unfold Fresh', '  decide +kernel',
                  f'private theorem disjoint{i} : ∀ j ∈ List.range {k}, {i} ≠ j →',
                  f'    ∀ x ∈ domains {i}, x ∉ domains j := by', '  decide +kernel']
    lines += [f'theorem fresh_domains : ∀ i ∈ List.range {k}, ∀ x ∈ domains i,',
              '    Fresh 196 maker breaker x := by', '  intro i hi'] + index_cases(k)
    lines += [f'  · exact fresh{i}' for i in range(k)]
    lines += [f'theorem disjoint_domains : DomainsDisjoint {k} domains := by',
              '  intro i hi'] + index_cases(k)
    lines += [f'  · exact disjoint{i}' for i in range(k)]
    lines += [f'theorem component_defenses : ∀ i ∈ List.range {k},',
              '    ¬ BlackWins (targets i) 196 [] (outside 196 (domains i)) := by',
              '  intro i hi'] + index_cases(k)
    for a,b in pairs:
        lines += [f'  · exact pair_component_not_blackWins (N := 196) (a := {a}) (b := {b}) (by decide) (by decide) (by decide)']
    lines += ['  · exact C00.defense', '', f'end Snaky.Breaker{label}']
    write(f'Breaker{label}Data', lines)


def get_n32():
    r = read('verification/n32_reserved_controller.json')
    cs = r['phase_contexts']
    contexts = []
    for c in cs:
        contexts.append({'domain': cells(c['reserved_domain']), 'maker': cells(c['known_maker']),
                         'breaker': cells(c['known_breaker']),
                         'pairs': [cells(p) for p in c['exterior_pairs']], 'rows': []})
    for i,c in enumerate(cs):
        dom = set(contexts[i]['domain'])
        for row in c['rows']:
            if row.get('entry') is None:
                continue
            u,v = cell(row['entry']),cell(row['reply'])
            if u not in dom:
                continue
            out = {'u':u,'v':v}
            if 'next_phase' in row:
                matches = [j for j,d in enumerate(contexts) if d['maker'] == sorted(contexts[i]['maker']+[u])
                           and d['breaker'] == sorted(contexts[i]['breaker']+[v])]
                assert len(matches) == 1, (i,row,matches)
                out['child'] = matches[0]
                source_pairs = contexts[matches[0]]['pairs']
            else:
                source_pairs = [cells(p) for p in row['committed_pairs']]
            assert all(not (bool(set(p)&dom) and not set(p)<=dom) for p in source_pairs)
            # The physical report retains consumed old pairs in three rows.
            # A pair hit by this actual Breaker reply is retired; it cannot
            # protect a still-live local target and is not a fresh component.
            out['pairs'] = [p for p in source_pairs if set(p)<=dom and v not in p]
            contexts[i]['rows'].append(out)
    return contexts


def get_n33():
    r = read('verification/n33_k10_controller.json')
    m,b = cells(r['original_state']['maker']),cells(r['original_state']['breaker'])
    dom = cells(r['reserved_domain'])
    names = {k:cell(v) for k,v in r['reserved_names'].items()}
    ps = [cells(p) for p in r['exterior_pairs']]
    contexts = [dict(domain=dom,maker=m,breaker=b,pairs=ps,rows=[]),
                dict(domain=sorted(set(dom)-{names['k'],names['j']}),maker=sorted(m+[names['k']]),
                     breaker=sorted(b+[names['j']]),pairs=ps,rows=[])]
    for i,field in enumerate(('phase_I_policy','phase_II_policy')):
        for name,row in r[field].items():
            if name == 'outside_unmatched':
                continue
            out = {'u':names[name], 'v':cell(row['reply']), 'pairs':[cells(p) for p in row['pairs']]}
            if row['mode'] == 'phase_II':
                out['child'] = 1
            contexts[i]['rows'].append(out)
    return contexts


def main():
    assert len(EDGES) == 1040
    for label,contexts in (('N33',get_n33()),('N32',get_n32())):
        for c in contexts:
            c['guards'] = guards(c)
        for i in reversed(range(len(contexts))):
            context_source(label,i,contexts[i],contexts)
        whole_source(label,contexts[0])
        print(label, 'contexts',len(contexts),'local rows',sum(len(c['rows']) for c in contexts),
              'root guards',len(contexts[0]['guards']))


if __name__ == '__main__':
    main()
