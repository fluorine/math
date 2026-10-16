import Snaky.BreakerS11Coverage
import Snaky.Geometry10

namespace Snaky.BreakerS11
open Snaky.Breaker
theorem full_target_coverage :
    MatchingCovers (placements 10 10 snaky) 100 maker breaker mate := by
  rw [Geometry10.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 10 10 snaky) 100 maker breaker :=
  matching_not_blackWins colors_disjoint matching_ok full_target_coverage
end Snaky.BreakerS11
