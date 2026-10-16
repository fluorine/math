#!/usr/bin/env python3
"""Generate small kernel coverage proofs over the shared literal geometry.

This writes proof source only, not certificates or trusted results. Each part
is reduced by `decide +kernel`; append composition and the shared checked
placement equality recover the actual game geometry in the final modules.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent / 'Snaky'


def write_waiting(module, data, namespace, n, count, reserved, guards):
    lines = [f'import Snaky.{data}', 'import Snaky.BreakerCoverage',
             f'import Snaky.Geometry{n}Data', '',
             f'namespace Snaky.{namespace}', 'open Snaky.Breaker', '']
    for i in range(count):
        lines += [f'private theorem cover{i:02} :',
            f'    WaitingCovers Geometry{n}.part{i:02} {n*n} maker breaker',
            f'      {reserved} {guards} outsideMate := by',
            '  unfold WaitingCovers OuterDomain Fresh', '  decide +kernel', '']
    term = f'cover{count-1:02}'
    for i in reversed(range(count-1)):
        term = f'waitingCovers_append cover{i:02} ({term})'
    lines += ['theorem literal_coverage :',
        f'    WaitingCovers Geometry{n}.targets {n*n} maker breaker',
        f'      {reserved} {guards} outsideMate := by',
        f'  simpa only [Geometry{n}.targets, List.append_assoc] using ({term})', '',
        f'end Snaky.{namespace}', '']
    (HERE / f'{module}.lean').write_text('\n'.join(lines))


def write_matching(module, n, count):
    lines = [f'import Snaky.{module}Data', 'import Snaky.BreakerCoverage',
             f'import Snaky.Geometry{n}Data', '',
             f'namespace Snaky.{module}', 'open Snaky.Breaker', '']
    for i in range(count):
        lines += [f'private theorem cover{i:02} :',
            f'    MatchingCovers Geometry{n}.part{i:02} {n*n} maker breaker mate := by',
            '  unfold MatchingCovers Fresh', '  decide +kernel', '']
    term = f'cover{count-1:02}'
    for i in reversed(range(count-1)):
        term = f'matchingCovers_append cover{i:02} ({term})'
    lines += ['theorem literal_coverage :',
        f'    MatchingCovers Geometry{n}.targets {n*n} maker breaker mate := by',
        f'  simpa only [Geometry{n}.targets, List.append_assoc] using ({term})', '', f'end Snaky.{module}', '']
    (HERE / f'{module}Coverage.lean').write_text('\n'.join(lines))
    (HERE / f'{module}.lean').write_text(f'''import Snaky.{module}Coverage
import Snaky.Geometry{n}

namespace Snaky.{module}
open Snaky.Breaker
theorem full_target_coverage :
    MatchingCovers (placements {n} {n} snaky) {n*n} maker breaker mate := by
  rw [Geometry{n}.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements {n} {n} snaky) {n*n} maker breaker :=
  matching_not_blackWins colors_disjoint matching_ok full_target_coverage
end Snaky.{module}
''')


def write_product(module, n, count, components):
    lines = [f'import Snaky.{module}Data', 'import Snaky.BreakerProductCoverage',
             f'import Snaky.Geometry{n}Data', '',
             f'namespace Snaky.{module}', 'open Snaky.Breaker', '']
    for i in range(count):
        lines += [f'private theorem cover{i:02} : ProductCovers Geometry{n}.part{i:02} breaker {components} targets := by',
                  '  unfold ProductCovers', '  decide +kernel', '']
    term = f'cover{count-1:02}'
    for i in reversed(range(count-1)):
        term = f'productCovers_append cover{i:02} ({term})'
    lines += [f'theorem literal_coverage : ProductCovers Geometry{n}.targets breaker {components} targets := by',
              f'  simpa only [Geometry{n}.targets, List.append_assoc] using ({term})', '',
              f'end Snaky.{module}', '']
    (HERE / f'{module}Coverage.lean').write_text('\n'.join(lines))
    (HERE / f'{module}.lean').write_text(f'''import Snaky.{module}Coverage
import Snaky.Geometry{n}

namespace Snaky.{module}
open Snaky.Breaker
theorem full_target_coverage : ProductCovers (placements {n} {n} snaky) breaker {components} targets := by
  rw [Geometry{n}.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements {n} {n} snaky) {n*n} maker breaker := by
  apply product_not_blackWins colors_disjoint fresh_domains disjoint_domains
  · intro i hi g hg; exact (shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (shapes i hi)
  · exact component_defenses
  · exact full_target_coverage
end Snaky.{module}
''')


def main():
    write_waiting('P52Coverage', 'P52Data', 'P52', 10, 80, 'reserved', 'guards')
    write_waiting('P52Continued52Coverage', 'P52ContinuedData',
                  'P52Continued.Endpoint52', 10, 80, 'P52.reserved', 'P52.guards')
    write_waiting('P52Continued53Coverage', 'P52ContinuedData',
                  'P52Continued.Endpoint53', 10, 80, 'P52.reserved', 'P52.guards')
    for module in ('BreakerS11', 'BreakerS13', 'BreakerPostM31', 'BreakerP53Leaf'):
        write_matching(module, 10, 80)
    write_matching('BreakerLRow', 14, 112)
    write_waiting('BreakerLCapCoverage', 'BreakerLCapData', 'BreakerLCap', 14, 112, 'reserved', 'guards')
    (HERE / 'BreakerLCap.lean').write_text('''import Snaky.BreakerLCapCoverage
import Snaky.Geometry14

namespace Snaky.BreakerLCap
open Snaky.Breaker
theorem full_target_coverage : WaitingCovers (placements 14 14 snaky) 196 maker breaker reserved guards outsideMate := by
  rw [Geometry14.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 14 14 snaky) 196 maker breaker :=
  pristine_switch_not_blackWins colors_disjoint reserved_fresh exterior_matching guard_shape switch_rows full_target_coverage
end Snaky.BreakerLCap
''')
    write_product('BreakerN33', 14, 112, 52)
    write_product('BreakerN32', 14, 112, 47)


if __name__ == '__main__':
    main()
