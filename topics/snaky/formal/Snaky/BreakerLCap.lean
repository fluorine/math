import Snaky.BreakerLCapCoverage
import Snaky.Geometry14

namespace Snaky.BreakerLCap
open Snaky.Breaker
theorem full_target_coverage : WaitingCovers (placements 14 14 snaky) 196 maker breaker reserved guards outsideMate := by
  rw [Geometry14.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 14 14 snaky) 196 maker breaker :=
  pristine_switch_not_blackWins colors_disjoint reserved_fresh exterior_matching guard_shape switch_rows full_target_coverage
end Snaky.BreakerLCap
