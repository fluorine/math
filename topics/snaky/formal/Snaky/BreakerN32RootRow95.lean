import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row95Domains : Nat → List Nat
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
private def row95Targets : Nat → List (List Nat)
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
theorem row95Fresh : Fresh 196 [95] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row95Colors : Disjoint [95] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row95DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row95Domains i,
    Fresh 196 [95] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row95Disjoint : DomainsDisjoint 9 row95Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row95Shapes : ∀ i ∈ List.range 9, GuardOK (row95Domains i) (row95Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row95Covers : ProductCovers guards (68 :: outside 196 domain) 9 row95Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row95Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row95Targets i) 196 [] (outside 196 (row95Domains i)) := by
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
theorem row95Defense : ¬ BlackWins guards 196 [95] (68 :: outside 196 domain) := by
  apply product_not_blackWins row95Colors row95DomainsFresh row95Disjoint
  · intro i hi g hg; exact (row95Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row95Shapes i hi)
  · exact row95Components
  · exact row95Covers


end Snaky.BreakerN32.C00
