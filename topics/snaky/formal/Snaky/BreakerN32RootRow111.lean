import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row111Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [96,109]
  | 6 => [123,124]
  | 7 => [108,110]
  | 8 => [125,139]
  | _ => []
private def row111Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[96,109]]
  | 6 => [[123,124]]
  | 7 => [[108,110]]
  | 8 => [[125,139]]
  | _ => []
theorem row111Fresh : Fresh 196 [111] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row111Colors : Disjoint [111] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row111DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row111Domains i,
    Fresh 196 [111] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row111Disjoint : DomainsDisjoint 9 row111Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row111Shapes : ∀ i ∈ List.range 9, GuardOK (row111Domains i) (row111Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row111Covers : ProductCovers guards (68 :: outside 196 domain) 9 row111Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row111Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row111Targets i) 196 [] (outside 196 (row111Domains i)) := by
  intro i hi
  have hiN : i < 9 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 123) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
theorem row111Defense : ¬ BlackWins guards 196 [111] (68 :: outside 196 domain) := by
  apply product_not_blackWins row111Colors row111DomainsFresh row111Disjoint
  · intro i hi g hg; exact (row111Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row111Shapes i hi)
  · exact row111Components
  · exact row111Covers


end Snaky.BreakerN32.C00
