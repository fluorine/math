import Snaky.BreakerN33Coverage
import Snaky.Geometry14

namespace Snaky.BreakerN33
open Snaky.Breaker
theorem full_target_coverage : ProductCovers (placements 14 14 snaky) breaker 52 targets := by
  rw [Geometry14.placements_eq_targets]
  exact literal_coverage
theorem not_blackWins : ¬ BlackWins (placements 14 14 snaky) 196 maker breaker := by
  apply product_not_blackWins colors_disjoint fresh_domains disjoint_domains
  · intro i hi g hg; exact (shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (shapes i hi)
  · exact component_defenses
  · exact full_target_coverage
end Snaky.BreakerN33
