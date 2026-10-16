import Snaky.P52Continued52Coverage
import Snaky.P52Continued53Coverage
import Snaky.Geometry10

/-! These are the two accepted continued endpoints, with their entire old
colors retained. In particular the second theorem does not resolve the
earlier original P53 position or S9. -/
namespace Snaky.P52Continued
open Snaky.Breaker

namespace Endpoint52
theorem full_target_coverage :
    WaitingCovers (placements 10 10 snaky) 100 maker breaker
      P52.reserved P52.guards outsideMate := by
  rw [Geometry10.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 10 10 snaky) 100 maker breaker :=
  pristine_switch_not_blackWins colors_disjoint reserved_fresh exterior_matching
    P52.guard_shape P52.switch_rows full_target_coverage
end Endpoint52

namespace Endpoint53
theorem full_target_coverage :
    WaitingCovers (placements 10 10 snaky) 100 maker breaker
      P52.reserved P52.guards outsideMate := by
  rw [Geometry10.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 10 10 snaky) 100 maker breaker :=
  pristine_switch_not_blackWins colors_disjoint reserved_fresh exterior_matching
    P52.guard_shape P52.switch_rows full_target_coverage
end Endpoint53

end Snaky.P52Continued
