import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row54Domains : Nat → List Nat
  | 0 => [27,41]
  | 1 => [52,53]
  | 2 => [67,81]
  | 3 => [69,83]
  | 4 => [26,40]
  | 5 => [108,109]
  | 6 => [110,124]
  | 7 => [111,139]
  | 8 => [96,123]
  | _ => []
private def row54Targets : Nat → List (List Nat)
  | 0 => [[27,41]]
  | 1 => [[52,53]]
  | 2 => [[67,81]]
  | 3 => [[69,83]]
  | 4 => [[26,40]]
  | 5 => [[108,109]]
  | 6 => [[110,124]]
  | 7 => [[111,139]]
  | 8 => [[96,123]]
  | _ => []
theorem row54Fresh : Fresh 196 [54] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row54Colors : Disjoint [54] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row54DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row54Domains i,
    Fresh 196 [54] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row54Disjoint : DomainsDisjoint 9 row54Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row54Shapes : ∀ i ∈ List.range 9, GuardOK (row54Domains i) (row54Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row54Covers : ProductCovers guards (68 :: outside 196 domain) 9 row54Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row54Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row54Targets i) 196 [] (outside 196 (row54Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 40) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
theorem row54Defense : ¬ BlackWins guards 196 [54] (68 :: outside 196 domain) := by
  apply product_not_blackWins row54Colors row54DomainsFresh row54Disjoint
  · intro i hi g hg; exact (row54Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row54Shapes i hi)
  · exact row54Components
  · exact row54Covers


end Snaky.BreakerN32.C00
