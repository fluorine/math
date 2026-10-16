import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row139Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [96,123]
  | 6 => [108,109]
  | 7 => [110,125]
  | 8 => [97,111]
  | _ => []
private def row139Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[96,123]]
  | 6 => [[108,109]]
  | 7 => [[110,125]]
  | 8 => [[97,111]]
  | _ => []
theorem row139Fresh : Fresh 196 [139] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row139Colors : Disjoint [139] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row139DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row139Domains i,
    Fresh 196 [139] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row139Disjoint : DomainsDisjoint 9 row139Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row139Shapes : ∀ i ∈ List.range 9, GuardOK (row139Domains i) (row139Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row139Covers : ProductCovers guards (68 :: outside 196 domain) 9 row139Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row139Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row139Targets i) 196 [] (outside 196 (row139Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
theorem row139Defense : ¬ BlackWins guards 196 [139] (68 :: outside 196 domain) := by
  apply product_not_blackWins row139Colors row139DomainsFresh row139Disjoint
  · intro i hi g hg; exact (row139Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row139Shapes i hi)
  · exact row139Components
  · exact row139Covers

end Snaky.BreakerN32.C00
