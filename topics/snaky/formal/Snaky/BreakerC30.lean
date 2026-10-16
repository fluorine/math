import Snaky.BreakerC30Coverage
import Snaky.Geometry10

namespace Snaky.BreakerC30
open Snaky.Breaker

theorem full_target_coverage : ProductCovers (placements 10 10 snaky) breaker 27 targets := by
  rw [Geometry10.placements_eq_targets]
  exact literal_coverage

/-- Twelve complete physical conditional defenses, including arbitrary
outside interleavings, extra Breaker fillers and the last Maker claim. -/
theorem not_blackWins (z : Nat) (hz : z ∈ entries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (z :: maker₀) breaker := by
  apply product_not_blackWins (colors_disjoint z hz) (fresh_domains z hz) disjoint_domains
  · intro i hi g hg
    exact (shapes i hi g hg).1
  · intro i hi
    exact guard_noComplete_empty (shapes i hi)
  · exact component_defenses
  · exact full_target_coverage

end Snaky.BreakerC30
