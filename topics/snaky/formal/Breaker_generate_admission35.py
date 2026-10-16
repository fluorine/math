#!/usr/bin/env python3
"""Emit kernel proof obligations for 35 accepted A52 successor states.

The seven unresolved parent entries are deliberately absent. Each exported
state is Maker to move after the displayed first entry and actual B33 reply.
All literals are untrusted until the ordinary switch theorem is instantiated.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent/'board_size/verification/browser_twentysixth_admission04.json'
PIN = '0520e70ef225c078d0667d1f0ada0d8888aef9f5327de4a38a387acd25016872'


def lit(xs):
    return '['+','.join(map(str,xs))+']'


def write(name,lines):
    p=ROOT/'Snaky'/(name+'.lean');text='\n'.join(lines)+'\n'
    if p.exists():
        assert p.read_text()==text, f'refusing changed existing source {name}'
    else:
        p.write_text(text)


def main():
    raw=SOURCE.read_bytes();assert hashlib.sha256(raw).hexdigest()==PIN
    r=json.loads(raw);rows=r['admission']['rows'];assert len(rows)==35
    entries=[a['first_maker'] for a in rows]
    base=sorted(set(rows[0]['state']['maker'])-{entries[0]});b=rows[0]['state']['breaker']
    assert len(base)==10 and len(b)==11
    for a in rows:
        assert a['state']['maker']==sorted(base+[a['first_maker']])
        assert a['state']['breaker']==b and a['reply']==33
    lines=['import Snaky.P52Data','','namespace Snaky.BreakerAdmission35','open Snaky.Breaker',
           f'def entries : List Nat := {lit(entries)}',f'def maker₀ : List Nat := {lit(base)}',
           'def maker (u : Nat) : List Nat := u :: maker₀',f'def breaker : List Nat := {lit(b)}',
           'def outsidePairs : Nat → List (Nat × Nat)']
    for a in rows:
        ps=','.join(f'({x},{y})' for x,y in a['outside_pairs'])
        lines += [f'  | {a["first_maker"]} => [{ps}]']
    lines += ['  | _ => []','def outsideMate (u : Nat) := mateOfPairs (outsidePairs u)',
              'theorem colors_disjoint : ∀ u ∈ entries, Disjoint (maker u) breaker := by',
              '  unfold Disjoint','  decide +kernel',
              'theorem reserved_fresh : ∀ u ∈ entries, ∀ x ∈ P52.reserved, Fresh 100 (maker u) breaker x := by',
              '  unfold Fresh','  decide +kernel','','end Snaky.BreakerAdmission35']
    write('BreakerAdmission35Data',lines)
    for group in range(7):
        es=entries[5*group:5*group+5]
        ns=f'Snaky.BreakerAdmission35.G{group}'
        lines=['import Snaky.BreakerAdmission35Data','import Snaky.BreakerCoverage',
               'import Snaky.Geometry10Data','',f'namespace {ns}','open Snaky.Breaker',
               f'def groupEntries : List Nat := {lit(es)}','']
        for u in es:
            for low in range(0,100,20):
                high=low+20
                lines += [f'private theorem mate{u}_{low} : ∀ x ∈ List.range {high}, {low} ≤ x →',
                    f'    x ∉ maker {u} → x ∉ breaker → x ∉ P52.reserved →',
                    f'    Fresh 100 (maker {u}) breaker (outsideMate {u} x) ∧',
                    f'    outsideMate {u} x ∉ P52.reserved ∧ outsideMate {u} x ≠ x ∧',
                    f'    outsideMate {u} (outsideMate {u} x) = x := by',
                    '  unfold Fresh','  decide +kernel','']
            lines += [f'private theorem matching{u} : OuterOK 100 (maker {u}) breaker P52.reserved (outsideMate {u}) := by',
                      '  intro x hx hm hb hr','  have h100 : x < 100 := List.mem_range.mp hx']
            for high in (20,40,60,80):
                lines += [f'  by_cases h{high} : x < {high}',f'  · exact mate{u}_{high-20} x (List.mem_range.mpr h{high}) (by omega) hm hb hr']
            lines += [f'  exact mate{u}_80 x (List.mem_range.mpr h100) (by omega) hm hb hr','']
        lines += ['theorem matching : ∀ u ∈ groupEntries, OuterOK 100 (maker u) breaker P52.reserved (outsideMate u) := by',
                  '  intro u hu','  have cases : '+' ∨ '.join(f'u = {u}' for u in es)+' := by',
                  '    simpa only [groupEntries,List.mem_cons,List.not_mem_nil,or_false] using hu',
                  '  rcases cases with '+' | '.join('rfl' for _ in es)]
        lines += [f'  · exact matching{u}' for u in es]
        for i in range(80):
            lines += ['',f'private theorem cover{i:02} : ∀ u ∈ groupEntries,',
                f'    WaitingCovers Geometry10.part{i:02} 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by',
                '  unfold WaitingCovers OuterDomain Fresh','  decide +kernel']
        term='cover79 u hu'
        for i in reversed(range(79)):
            term=f'waitingCovers_append (cover{i:02} u hu) ({term})'
        lines += ['', 'theorem literal_coverage (u : Nat) (hu : u ∈ groupEntries) :',
                  '    WaitingCovers Geometry10.targets 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by',
                  f'  simpa only [Geometry10.targets,List.append_assoc] using ({term})',
                  '',f'end {ns}']
        write(f'BreakerAdmission35Group{group}',lines)
    lines=[f'import Snaky.BreakerAdmission35Group{i}' for i in range(7)]
    lines+=['import Snaky.Geometry10','','namespace Snaky.BreakerAdmission35','open Snaky.Breaker','']
    for group in range(7):
        lines += [f'private theorem group{group}_defense (u : Nat) (hu : u ∈ G{group}.groupEntries) :',
                  '    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by',
                  f'  have he : u ∈ entries := by',
                  f'    have h : ∀ x ∈ G{group}.groupEntries, x ∈ entries := by decide +kernel',
                  '    exact h u hu',
                  f'  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)',
                  f'    (G{group}.matching u hu) P52.guard_shape P52.switch_rows',
                  '  rw [Geometry10.placements_eq_targets]',f'  exact G{group}.literal_coverage u hu','']
    lines += ['/-- Thirty-five complete conditional successor defenses, not a complete A52 root. -/',
              'theorem not_blackWins (u : Nat) (hu : u ∈ entries) :',
              '    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by',
              '  have cases : '+' ∨ '.join(f'u = {u}' for u in entries)+' := by',
              '    simpa only [entries,List.mem_cons,List.not_mem_nil,or_false] using hu',
              '  rcases cases with '+' | '.join('rfl' for _ in entries)]
    lines += [f'  · exact group{i//5}_defense {u} (by decide)' for i,u in enumerate(entries)]
    lines += ['','end Snaky.BreakerAdmission35']
    write('BreakerAdmission35',lines)


if __name__=='__main__':
    main()
