import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row55Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [108,109]
  | 6 => [110,124]
  | 7 => [111,139]
  | 8 => [96,123]
  | _ => []
private def row55Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[108,109]]
  | 6 => [[110,124]]
  | 7 => [[111,139]]
  | 8 => [[96,123]]
  | _ => []
theorem row55Fresh : Fresh 196 [55] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row55Colors : Disjoint [55] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row55DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row55Domains i,
    Fresh 196 [55] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row55Disjoint : DomainsDisjoint 9 row55Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row55Shapes : ∀ i ∈ List.range 9, GuardOK (row55Domains i) (row55Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row55Covers : ProductCovers guards (68 :: outside 196 domain) 9 row55Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row55Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row55Targets i) 196 [] (outside 196 (row55Domains i)) := by
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
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
theorem row55Defense : ¬ BlackWins guards 196 [55] (68 :: outside 196 domain) := by
  apply product_not_blackWins row55Colors row55DomainsFresh row55Disjoint
  · intro i hi g hg; exact (row55Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row55Shapes i hi)
  · exact row55Components
  · exact row55Covers


end Snaky.BreakerN32.C00
