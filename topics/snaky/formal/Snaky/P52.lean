import Snaky.P52Coverage
import Snaky.Geometry10

namespace Snaky.P52
open Snaky.Breaker

theorem full_target_coverage :
    WaitingCovers (placements 10 10 snaky) 100 maker breaker reserved guards outsideMate := by
  rw [Geometry10.placements_eq_targets]
  exact literal_coverage

/-- Breaker prevents every literal Snaky from the original P52 Maker turn. -/
theorem not_blackWins : ¬ BlackWins (placements 10 10 snaky) 100 maker breaker :=
  pristine_switch_not_blackWins colors_disjoint reserved_fresh exterior_matching
    guard_shape switch_rows full_target_coverage

end Snaky.P52
