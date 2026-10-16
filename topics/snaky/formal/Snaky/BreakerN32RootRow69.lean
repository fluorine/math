import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row69Domains : Nat → List Nat
  | 0 => [40,54]
  | 1 => [41,55]
  | 2 => [52,67]
  | 3 => [95,109]
  | 4 => [108,124]
  | 5 => [96,110]
  | 6 => [97,111]
  | _ => []
private def row69Targets : Nat → List (List Nat)
  | 0 => [[40,54]]
  | 1 => [[41,55]]
  | 2 => [[52,67]]
  | 3 => [[95,109]]
  | 4 => [[108,124]]
  | 5 => [[96,110]]
  | 6 => [[97,111]]
  | _ => []
theorem row69Fresh : Fresh 196 [69] (outside 196 domain) 53 := by
  unfold Fresh
  decide +kernel
private theorem row69Colors : Disjoint [69] (53 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row69DomainsFresh : ∀ i ∈ List.range 7, ∀ x ∈ row69Domains i,
    Fresh 196 [69] (53 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row69Disjoint : DomainsDisjoint 7 row69Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row69Shapes : ∀ i ∈ List.range 7, GuardOK (row69Domains i) (row69Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row69Covers : ProductCovers guards (53 :: outside 196 domain) 7 row69Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row69Components : ∀ i ∈ List.range 7,
    ¬ BlackWins (row69Targets i) 196 [] (outside 196 (row69Domains i)) := by
  intro i hi
  have hiN : i < 7 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 41) (b := 55) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 67) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
theorem row69Defense : ¬ BlackWins guards 196 [69] (53 :: outside 196 domain) := by
  apply product_not_blackWins row69Colors row69DomainsFresh row69Disjoint
  · intro i hi g hg; exact (row69Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row69Shapes i hi)
  · exact row69Components
  · exact row69Covers


end Snaky.BreakerN32.C00
