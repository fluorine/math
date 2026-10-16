import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row68Domains : Nat → List Nat
  | 0 => [27,41]
  | 1 => [52,67]
  | 2 => [53,54]
  | 3 => [26,40]
  | 4 => [81,95]
  | 5 => [83,97]
  | 6 => [108,109]
  | _ => []
private def row68Targets : Nat → List (List Nat)
  | 0 => [[27,41]]
  | 1 => [[52,67]]
  | 2 => [[53,54]]
  | 3 => [[26,40]]
  | 4 => [[81,95]]
  | 5 => [[83,97]]
  | 6 => [[108,109]]
  | _ => []
theorem row68Fresh : Fresh 196 [68] (outside 196 domain) 96 := by
  unfold Fresh
  decide +kernel
private theorem row68Colors : Disjoint [68] (96 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row68DomainsFresh : ∀ i ∈ List.range 7, ∀ x ∈ row68Domains i,
    Fresh 196 [68] (96 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row68Disjoint : DomainsDisjoint 7 row68Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row68Shapes : ∀ i ∈ List.range 7, GuardOK (row68Domains i) (row68Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row68Covers : ProductCovers guards (96 :: outside 196 domain) 7 row68Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row68Components : ∀ i ∈ List.range 7,
    ¬ BlackWins (row68Targets i) 196 [] (outside 196 (row68Domains i)) := by
  intro i hi
  have hiN : i < 7 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 67) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 53) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 40) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 81) (b := 95) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 83) (b := 97) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
theorem row68Defense : ¬ BlackWins guards 196 [68] (96 :: outside 196 domain) := by
  apply product_not_blackWins row68Colors row68DomainsFresh row68Disjoint
  · intro i hi g hg; exact (row68Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row68Shapes i hi)
  · exact row68Components
  · exact row68Covers


end Snaky.BreakerN32.C00
