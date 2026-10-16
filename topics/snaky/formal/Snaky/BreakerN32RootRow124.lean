import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row124Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [96,110]
  | 6 => [108,109]
  | 7 => [95,123]
  | 8 => [111,139]
  | _ => []
private def row124Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[96,110]]
  | 6 => [[108,109]]
  | 7 => [[95,123]]
  | 8 => [[111,139]]
  | _ => []
theorem row124Fresh : Fresh 196 [124] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row124Colors : Disjoint [124] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row124DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row124Domains i,
    Fresh 196 [124] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row124Disjoint : DomainsDisjoint 9 row124Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row124Shapes : ∀ i ∈ List.range 9, GuardOK (row124Domains i) (row124Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row124Covers : ProductCovers guards (68 :: outside 196 domain) 9 row124Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row124Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row124Targets i) 196 [] (outside 196 (row124Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
theorem row124Defense : ¬ BlackWins guards 196 [124] (68 :: outside 196 domain) := by
  apply product_not_blackWins row124Colors row124DomainsFresh row124Disjoint
  · intro i hi g hg; exact (row124Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row124Shapes i hi)
  · exact row124Components
  · exact row124Covers


end Snaky.BreakerN32.C00
