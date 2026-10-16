#!/usr/bin/env python3
"""Generate Lean source for the twelve accepted C30 B43 endpoints.

The report supplies only literals. The generated ordinary game theorems use
kernel-checked local rows, the semantic disjoint-product theorem, and the exact
kernel-linked Snaky placements. No report status is a proof assumption.
"""
import hashlib
import json
from pathlib import Path

FORMAL = Path(__file__).resolve().parent
SOURCE = FORMAL.parent / 'board_size/verification/browser-twentyfourth-partition04-02.json'
PIN = '85f8f26a67056b046103ac8d79d940c065ff4d11b9348b68a4e227fbb7fa9c5e'


def literal(value):
    if isinstance(value, list):
        return '[' + ','.join(map(literal, value)) + ']'
    return str(value)


def write(name, lines):
    text = '\n'.join(lines) + '\n'
    path = FORMAL / 'Snaky' / name
    if path.exists():
        assert path.read_text() == text, 'refusing changed existing generated source'
    else:
        path.write_text(text)


def entry_cases(var, domain, hypothesis):
    return [f'  have cases : ' + ' ∨ '.join(f'{var} = {u}' for u in domain) + ' := by',
            f'    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using {hypothesis}',
            '  rcases cases with ' + ' | '.join('rfl' for _ in domain)]


def component(name, data):
    rows = sorted(data['rows'], key=lambda r: r['maker'])
    lines = [f'namespace {name}',
             f'def domain : List Nat := {literal(data["domain"])}',
             f'def guards : List (List Nat) := {literal(data["targets"])}',
             'def reply : Nat → Nat']
    lines += [f'  | {r["maker"]} => {r["reply"]}' for r in rows]
    lines += ['  | u => u', 'def localPairs : Nat → List (Nat × Nat)']
    for r in rows:
        assert all(set(c) == {'pair'} for c in r['children'])
        ps = ','.join(f'({c["pair"][0]},{c["pair"][1]})' for c in r['children'])
        lines += [f'  | {r["maker"]} => [{ps}]']
    lines += ['  | _ => []',
              'def localDomain (u : Nat) : List Nat := (localPairs u).flatMap (fun p => [p.1,p.2])',
              'def localMate (u : Nat) := mateOfPairs (localPairs u)',
              'theorem shape : GuardOK domain guards := by',
              '  unfold GuardOK', '  decide +kernel', '']
    for r in rows:
        u = r['maker']
        lines += [f'private theorem row{u} :',
                  f'    Fresh 100 [{u}] (outside 100 domain) (reply {u}) ∧',
                  f'    PartialOK 100 [{u}] (reply {u} :: outside 100 domain) (localDomain {u}) (localMate {u}) ∧',
                  f'    PartialCovers guards [{u}] (reply {u} :: outside 100 domain) (localDomain {u}) (localMate {u}) := by',
                  '  unfold PartialOK PartialCovers Fresh', '  decide +kernel', '']
    lines += ['theorem rows : LocalReplyOK guards 100 domain reply localDomain localMate := by',
              '  intro u hu'] + entry_cases('u', data['domain'], 'hu')
    lines += [f'  · exact row{u}' for u in data['domain']]
    lines += ['theorem defense : ¬ BlackWins guards 100 [] (outside 100 domain) :=',
              '  local_reply_not_blackWins shape rows', f'end {name}', '']
    return lines


def main():
    raw = SOURCE.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PIN
    report = json.loads(raw)
    pairs = report['partition']['outside_pairs'] + report['exit_B43']['mid_pairs']
    entries = report['partition']['unassigned_cells']
    state = report['binding']['physical_state']
    assert len(pairs) == 25 and len(entries) == 12
    assert sorted(b['maker_entry'] for b in report['exit_B43']['branches']) == entries
    for branch in report['exit_B43']['branches']:
        assert branch['actual_state']['maker'] == sorted(state['maker'] + [branch['maker_entry']])
        assert branch['actual_state']['breaker'] == sorted(state['breaker'] + [43])
    lines = ['import Snaky.BreakerComponent', '',
             '/-! Twelve complete conditional physical defenses after Mz/B43.',
             'The original 9+9 colors, full domains and both local controllers',
             'are explicit. The original C30 root is not a theorem here. -/',
             'namespace Snaky.BreakerC30', 'open Snaky.Breaker', '',
             f'def maker₀ : List Nat := {literal(state["maker"])}',
             f'def breaker : List Nat := {literal(sorted(state["breaker"]+[43]))}',
             f'def entries : List Nat := {literal(entries)}', '']
    for name in ('R', 'T'):
        lines += component(name, report['certificate']['definitions'][name])
    lines += ['def domains : Nat → List Nat']
    lines += [f'  | {i} => {literal(p)}' for i, p in enumerate(pairs)]
    lines += ['  | 25 => R.domain', '  | 26 => T.domain', '  | _ => []',
              'def targets : Nat → List (List Nat)']
    lines += [f'  | {i} => [{literal(p)}]' for i, p in enumerate(pairs)]
    lines += ['  | 25 => R.guards', '  | 26 => T.guards', '  | _ => []', '',
              'theorem colors_disjoint : ∀ z ∈ entries, Disjoint (z :: maker₀) breaker := by',
              '  unfold Disjoint', '  decide +kernel', '',
              'theorem shapes : ∀ i ∈ List.range 27, GuardOK (domains i) (targets i) := by',
              '  unfold GuardOK', '  decide +kernel', '']
    # These statements include all 27 components; splitting bounds proof memory.
    for z in entries:
        lines += [f'private theorem fresh{z} : ∀ i ∈ List.range 27, ∀ x ∈ domains i,',
                  f'    Fresh 100 ({z} :: maker₀) breaker x := by',
                  '  unfold Fresh', '  decide +kernel', '']
    lines += ['theorem fresh_domains : ∀ z ∈ entries, ∀ i ∈ List.range 27, ∀ x ∈ domains i,',
              '    Fresh 100 (z :: maker₀) breaker x := by', '  intro z hz',
              '  have cases : ' + ' ∨ '.join(f'z = {z}' for z in entries) + ' := by',
              '    simpa only [entries, List.mem_cons, List.not_mem_nil, or_false] using hz',
              '  rcases cases with ' + ' | '.join('rfl' for _ in entries)]
    lines += [f'  · exact fresh{z}' for z in entries]
    for i in range(27):
        lines += ['', f'private theorem disjoint{i} : ∀ j ∈ List.range 27, {i} ≠ j →',
                  f'    ∀ x ∈ domains {i}, x ∉ domains j := by', '  decide +kernel']
    lines += ['', 'theorem disjoint_domains : DomainsDisjoint 27 domains := by',
              '  intro i hi', '  have hiN : i < 27 := List.mem_range.mp hi',
              '  have cases : ' + ' ∨ '.join(f'i = {i}' for i in range(27)) + ' := by omega',
              '  rcases cases with ' + ' | '.join('rfl' for _ in range(27))]
    lines += [f'  · exact disjoint{i}' for i in range(27)]
    lines += ['', 'theorem component_defenses : ∀ i ∈ List.range 27,',
              '    ¬ BlackWins (targets i) 100 [] (outside 100 (domains i)) := by',
              '  intro i hi', '  have hiN : i < 27 := List.mem_range.mp hi',
              '  have cases : ' + ' ∨ '.join(f'i = {i}' for i in range(27)) + ' := by omega',
              '  rcases cases with ' + ' | '.join('rfl' for _ in range(27))]
    for a, b in pairs:
        lines += [f'  · exact pair_component_not_blackWins (N := 100) (a := {a}) (b := {b}) (by decide) (by decide) (by decide)']
    lines += ['  · exact R.defense', '  · exact T.defense', '', 'end Snaky.BreakerC30']
    write('BreakerC30Data.lean', lines)

    cover = ['import Snaky.BreakerC30Data', 'import Snaky.BreakerProductCoverage',
             'import Snaky.Geometry10Data', '', 'namespace Snaky.BreakerC30',
             'open Snaky.Breaker', '']
    for i in range(80):
        cover += [f'private theorem cover{i:02} : ProductCovers Geometry10.part{i:02} breaker 27 targets := by',
                  '  unfold ProductCovers', '  decide +kernel', '']
    term = 'cover79'
    for i in reversed(range(79)):
        term = f'productCovers_append cover{i:02} ({term})'
    cover += ['theorem literal_coverage : ProductCovers Geometry10.targets breaker 27 targets := by',
              f'  simpa only [Geometry10.targets, List.append_assoc] using ({term})', '', 'end Snaky.BreakerC30']
    write('BreakerC30Coverage.lean', cover)
    write('BreakerC30.lean', ['import Snaky.BreakerC30Coverage', 'import Snaky.Geometry10', '',
        'namespace Snaky.BreakerC30', 'open Snaky.Breaker', '',
        'theorem full_target_coverage : ProductCovers (placements 10 10 snaky) breaker 27 targets := by',
        '  rw [Geometry10.placements_eq_targets]', '  exact literal_coverage', '',
        '/-- Twelve complete physical conditional defenses, including arbitrary',
        'outside interleavings, extra Breaker fillers and the last Maker claim. -/',
        'theorem not_blackWins (z : Nat) (hz : z ∈ entries) :',
        '    ¬ BlackWins (placements 10 10 snaky) 100 (z :: maker₀) breaker := by',
        '  apply product_not_blackWins (colors_disjoint z hz) (fresh_domains z hz) disjoint_domains',
        '  · intro i hi g hg', '    exact (shapes i hi g hg).1',
        '  · intro i hi', '    exact guard_noComplete_empty (shapes i hi)',
        '  · exact component_defenses', '  · exact full_target_coverage', '',
        'end Snaky.BreakerC30'])


if __name__ == '__main__':
    main()
