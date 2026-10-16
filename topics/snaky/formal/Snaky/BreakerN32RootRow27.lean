import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row27Domains : Nat → List Nat
  | 0 => [52,53]
  | 1 => [67,81]
  | 2 => [69,83]
  | 3 => [40,54]
  | 4 => [41,55]
  | 5 => [108,109]
  | 6 => [110,124]
  | 7 => [111,139]
  | 8 => [96,123]
  | _ => []
private def row27Targets : Nat → List (List Nat)
  | 0 => [[52,53]]
  | 1 => [[67,81]]
  | 2 => [[69,83]]
  | 3 => [[40,54]]
  | 4 => [[41,55]]
  | 5 => [[108,109]]
  | 6 => [[110,124]]
  | 7 => [[111,139]]
  | 8 => [[96,123]]
  | _ => []
theorem row27Fresh : Fresh 196 [27] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row27Colors : Disjoint [27] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row27DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row27Domains i,
    Fresh 196 [27] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row27Disjoint : DomainsDisjoint 9 row27Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row27Shapes : ∀ i ∈ List.range 9, GuardOK (row27Domains i) (row27Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row27Covers : ProductCovers guards (68 :: outside 196 domain) 9 row27Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row27Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row27Targets i) 196 [] (outside 196 (row27Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 41) (b := 55) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
theorem row27Defense : ¬ BlackWins guards 196 [27] (68 :: outside 196 domain) := by
  apply product_not_blackWins row27Colors row27DomainsFresh row27Disjoint
  · intro i hi g hg; exact (row27Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row27Shapes i hi)
  · exact row27Components
  · exact row27Covers


end Snaky.BreakerN32.C00
