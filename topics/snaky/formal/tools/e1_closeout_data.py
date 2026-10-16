#!/usr/bin/env python3
"""Emit untrusted literal e1 data; all coverage and geometry are Lean obligations."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
REPORT = HERE.parent / 'board_size/verification/e1-phase-template-universal-01.json'
EXPECTED = 'c437e5c196161365d87beeaa2dae1b4eff88db7876be3a522fe8de3c1663fda3'


def lean(value):
    if isinstance(value, list):
        return '[' + ', '.join(map(lean, value)) + ']'
    if isinstance(value, tuple):
        return '(' + ', '.join(map(lean, value)) + ')'
    return str(value)


def main():
    raw = REPORT.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED
    report = json.loads(raw)
    traces = [entry['trace'] for entry in report['literal_source_inventory']['source_traces']]
    parts = [traces[i:i+24] for i in range(0, len(traces), 24)]
    out = ['import Snaky.E1Coverage', '', 'namespace Snaky.E1',
           'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    for i, part in enumerate(parts):
        out += [f'def sourcesPart{i:02d} : List (List Nat) := {lean(part)}']
    out += ['def sources : List (List Nat) := ' + ' ++ '.join(f'sourcesPart{i:02d}' for i in range(len(parts))), '']
    uncovered_modules = []
    glue = []
    matching = ['import Snaky.E1Data', '', 'namespace Snaky.E1',
                'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    for t in report['six_templates']:
        phase, mode = t['phase'], t['mode']
        pairs = [tuple(p) for p in t['pairs']]
        uncovered = [s for s in traces if not any(a in s and b in s for a, b in pairs)]
        stem = f'{phase}{mode}'
        out += [f'def pairs{stem} : List Pair := {lean(pairs)}',
                f'def uncovered{stem} : List (List Nat) := {lean(uncovered)}', '']
        matching += [f'theorem pairs{stem}_matching : ((pairs{stem}.flatMap fun p => [p.1, p.2]).Nodup) ∧',
                     f'    (∀ p ∈ pairs{stem}, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel', '']
        for i, part in enumerate(parts):
            module = f'E1Uncovered{stem}Part{i:02d}'
            uncovered_modules.append(module)
            missing = [s for s in part if not any(a in s and b in s for a, b in pairs)]
            (HERE / f'Snaky/{module}.lean').write_text(
                'import Snaky.E1Data\n\nnamespace Snaky.E1\n'
                'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
                f'theorem uncovered{stem}_part{i:02d} : sourcesPart{i:02d}.filter (fun t => !covered pairs{stem} t) = {lean(missing)} := by decide +kernel\n'
                '\nend Snaky.E1\n')
        glue += [f'theorem uncovered{stem}_exact : sources.filter (fun t => !covered pairs{stem} t) = uncovered{stem} := by',
                 '  simp only [sources, List.filter_append, ' + ', '.join(f'uncovered{stem}_part{i:02d}' for i in range(len(parts))) + ']',
                 '  rfl', '']
    out += ['end Snaky.E1', '']
    dest = HERE / 'Snaky/E1Data.lean'
    dest.write_text('\n'.join(out))
    matching += ['end Snaky.E1', '']
    (HERE / 'Snaky/E1Matching.lean').write_text('\n'.join(matching))
    (HERE / 'Snaky/E1Uncovered.lean').write_text('\n'.join(
        [f'import Snaky.{m}' for m in uncovered_modules] +
        ['', 'namespace Snaky.E1', ''] + glue + ['end Snaky.E1', '']))
    masks = []
    for mask in range(512):
        row = {30 + i for i in range(9) if mask >> i & 1}
        if sum(set(range(30+i, 34+i)) <= row for i in range(6)) <= 1:
            masks.append(mask)
    chunks = []
    for i, offset in enumerate(range(0, len(masks), 32)):
        name = f'E1Checks{i:02d}'
        chunks.append(name)
        subgroup_imports = []
        group = masks[offset:offset+32]
        for j, start in enumerate(range(0, len(group), 4)):
            subgroup = group[start:start+4]
            partname = f'E1Checks{i:02d}Part{j}'
            subgroup_imports.append(f'import Snaky.{partname}')
            (HERE / f'Snaky/{partname}.lean').write_text(
                'import Snaky.E1Conditions\n\nnamespace Snaky.E1\n'
                'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
                + ''.join(f'theorem mask{m}_checked : checkMask {m} = true := by decide +kernel\n' for m in subgroup)
                + '\nend Snaky.E1\n')
        (HERE / f'Snaky/{name}.lean').write_text(
            '\n'.join(subgroup_imports) + '\n\nnamespace Snaky.E1\n'
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
            f'def masks{i:02d} : List Nat := {lean(group)}\n'
            + f'theorem masks{i:02d}_checked : masks{i:02d}.all checkMask = true := by\n'
            + f'  simp only [masks{i:02d}, List.all_cons, List.all_nil, '
            + ', '.join(f'mask{m}_checked' for m in group)
            + ', Bool.and_self]\n\nend Snaky.E1\n')

    # Split the 512 row-pattern membership checks independently of the
    # smaller uncovered-source checks; proof imports preserve exact coverage.
    maskdata = ['namespace Snaky.E1', '']
    for j in range(16):
        block = list(range(32*j, 32*(j+1)))
        maskdata += [f'def inputMasks{j:02d} : List Nat := {lean(block)}',
                     f'def outputMasks{j:02d} : List Nat := {lean([m for m in block if m in masks])}']
        (HERE / f'Snaky/E1MaskInventoryPart{j:02d}.lean').write_text(
            'import Snaky.E1Conditions\nimport Snaky.E1MaskInventoryData\n\nnamespace Snaky.E1\n'
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
            f'theorem maskInventory{j:02d} : inputMasks{j:02d}.filter validRow = outputMasks{j:02d} := by decide +kernel\n'
            'end Snaky.E1\n')
    maskdata += ['end Snaky.E1', '']
    (HERE / 'Snaky/E1MaskInventoryData.lean').write_text('\n'.join(maskdata))
    maskglue = [f'import Snaky.E1MaskInventoryPart{j:02d}' for j in range(16)]
    maskglue += ['', 'namespace Snaky.E1', 'set_option maxRecDepth 100000',
                 'set_option maxHeartbeats 0', '',
                 f'theorem validMasks_literal : validMasks = {lean(masks)} := by',
                 '  have hr : List.range 512 = ' + ' ++ '.join(f'inputMasks{j:02d}' for j in range(16)) + ' := by decide +kernel',
                 '  change (List.range 512).filter validRow = _', '  rw [hr]',
                 '  simp only [List.filter_append, ' + ', '.join(f'maskInventory{j:02d}' for j in range(16)) + ']',
                 '  rfl', '', 'end Snaky.E1', '']
    (HERE / 'Snaky/E1MaskInventory.lean').write_text('\n'.join(maskglue))
    final = ['import Snaky.E1Geometry', 'import Snaky.E1ConfigCoverage', 'import Snaky.E1ConfigMatching', 'import Snaky.E1MaskInventory'] + [f'import Snaky.{name}' for name in chunks]
    final += ['', 'namespace Snaky.E1', 'set_option maxRecDepth 100000',
              'set_option maxHeartbeats 0', '',
              'def allMasks : List Nat := ' + ' ++ '.join(f'masks{i:02d}' for i in range(len(chunks))),
              'theorem validMasks_eq : validMasks = allMasks := by rw [validMasks_literal]; rfl',
              'theorem validMasks_count : validMasks.length = 463 := by rw [validMasks_literal]; decide +kernel',
              'theorem all_checked : validMasks.all checkMask = true := by',
              '  rw [validMasks_eq]',
              '  simp only [allMasks, List.all_append, ' + ', '.join(f'masks{i:02d}_checked' for i in range(len(chunks))) + ', Bool.and_self]', '',
              'theorem config_checked (mask mode : Nat) (hm : mask < 512)',
              '    (hv : validRow mask = true) (hmode : mode < 3) :',
              '    (sources.filter (fun t => !covered (config mask mode).pairs t)).all',
              '      (rejected (config mask mode)) = true := by',
              '  have hmask : mask ∈ validMasks := List.mem_filter.mpr ⟨List.mem_range.mpr hm, hv⟩',
              '  have h := List.all_eq_true.mp all_checked mask hmask',
              '  have hh := List.all_eq_true.mp h mode (List.mem_range.mpr hmode)',
              '  change (sources.filter (fun t => !covered (pairsFor (phase mask) mode) t)).all _ = true',
              '  rw [uncoveredFor_exact]',
              '  exact hh', '',
              '/-- Every active full eligible source is covered on the same entire core K.',
              'The explicit membership constraints are hypotheses. This is not a claim',
              'that all complete admissions satisfy them, or that the exterior is solved. -/',
              'theorem e1_source_replacement (mask mode : Nat) (hm : mask < 512)',
              '    (hv : validRow mask = true) (hmode : mode < 3)',
              '    {K F : List Nat} (hc : Compatible (config mask mode) K)',
              '    (hF : F ∈ placements 10 10 snaky) (he : eligible F = true)',
              '    (hactive : (traceOf F).Subset K) :',
              '    ∃ p ∈ (config mask mode).pairs,',
              '      p.1 ∈ traceOf F ∧ p.2 ∈ traceOf F ∧ p.1 ∈ K ∧ p.2 ∈ K :=',
              '  coverage_of_uncovered_check (config_checked mask mode hm hv hmode)',
              '    hc (sources_complete hF he) hactive', '',
              '/-- Any full-source incidence, including a different source, retains a pair. -/',
              'theorem e1_physical_incidence_replacement (mask mode : Nat) (hm : mask < 512)',
              '    (hv : validRow mask = true) (hmode : mode < 3)',
              '    {K F E : List Nat} (hc : Compatible (config mask mode) K)',
              '    (hF : F ∈ placements 10 10 snaky) (he : eligible F = true)',
              '    (hactive : (traceOf F).Subset K) (hinc : (traceOf F).Subset E) :',
              '    ∃ p ∈ (config mask mode).pairs,',
              '      p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ∈ E ∧ p.2 ∈ E :=',
              '  coverage_transfers (config_checked mask mode hm hv hmode)',
              '    hc (sources_complete hF he) hactive hinc', '',
              'end Snaky.E1', '']
    (HERE / 'Snaky/E1Result.lean').write_text('\n'.join(final))
    print(json.dumps({'output': str(dest), 'source_traces': len(traces),
                      'sha256': hashlib.sha256(dest.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
