import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row52Domains : Nat → List Nat
  | 0 => [40,54]
  | 1 => [41,55]
  | 2 => [67,81]
  | 3 => [68,69]
  | 4 => [95,109]
  | 5 => [108,124]
  | 6 => [96,110]
  | 7 => [97,111]
  | _ => []
private def row52Targets : Nat → List (List Nat)
  | 0 => [[40,54]]
  | 1 => [[41,55]]
  | 2 => [[67,81]]
  | 3 => [[68,69]]
  | 4 => [[95,109]]
  | 5 => [[108,124]]
  | 6 => [[96,110]]
  | 7 => [[97,111]]
  | _ => []
theorem row52Fresh : Fresh 196 [52] (outside 196 domain) 53 := by
  unfold Fresh
  decide +kernel
private theorem row52Colors : Disjoint [52] (53 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row52DomainsFresh : ∀ i ∈ List.range 8, ∀ x ∈ row52Domains i,
    Fresh 196 [52] (53 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row52Disjoint : DomainsDisjoint 8 row52Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row52Shapes : ∀ i ∈ List.range 8, GuardOK (row52Domains i) (row52Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row52Covers : ProductCovers guards (53 :: outside 196 domain) 8 row52Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row52Components : ∀ i ∈ List.range 8,
    ¬ BlackWins (row52Targets i) 196 [] (outside 196 (row52Domains i)) := by
  intro i hi
  have hiN : i < 8 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 41) (b := 55) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 68) (b := 69) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
theorem row52Defense : ¬ BlackWins guards 196 [52] (53 :: outside 196 domain) := by
  apply product_not_blackWins row52Colors row52DomainsFresh row52Disjoint
  · intro i hi g hg; exact (row52Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row52Shapes i hi)
  · exact row52Components
  · exact row52Covers


end Snaky.BreakerN32.C00
