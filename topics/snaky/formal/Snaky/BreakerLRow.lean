import Snaky.BreakerLRowCoverage
import Snaky.Geometry14

namespace Snaky.BreakerLRow
open Snaky.Breaker
theorem full_target_coverage :
    MatchingCovers (placements 14 14 snaky) 196 maker breaker mate := by
  rw [Geometry14.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 14 14 snaky) 196 maker breaker :=
  matching_not_blackWins colors_disjoint matching_ok full_target_coverage
end Snaky.BreakerLRow
