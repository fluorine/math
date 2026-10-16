import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row110Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [108,109]
  | 6 => [96,123]
  | 7 => [124,125]
  | 8 => [111,139]
  | _ => []
private def row110Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[108,109]]
  | 6 => [[96,123]]
  | 7 => [[124,125]]
  | 8 => [[111,139]]
  | _ => []
theorem row110Fresh : Fresh 196 [110] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row110Colors : Disjoint [110] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row110DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row110Domains i,
    Fresh 196 [110] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row110Disjoint : DomainsDisjoint 9 row110Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row110Shapes : ∀ i ∈ List.range 9, GuardOK (row110Domains i) (row110Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row110Covers : ProductCovers guards (68 :: outside 196 domain) 9 row110Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row110Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row110Targets i) 196 [] (outside 196 (row110Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 124) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
theorem row110Defense : ¬ BlackWins guards 196 [110] (68 :: outside 196 domain) := by
  apply product_not_blackWins row110Colors row110DomainsFresh row110Disjoint
  · intro i hi g hg; exact (row110Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row110Shapes i hi)
  · exact row110Components
  · exact row110Covers


end Snaky.BreakerN32.C00
