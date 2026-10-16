import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row67Domains : Nat → List Nat
  | 0 => [40,54]
  | 1 => [41,55]
  | 2 => [52,81]
  | 3 => [68,69]
  | 4 => [95,109]
  | 5 => [108,124]
  | 6 => [96,110]
  | 7 => [97,111]
  | _ => []
private def row67Targets : Nat → List (List Nat)
  | 0 => [[40,54]]
  | 1 => [[41,55]]
  | 2 => [[52,81]]
  | 3 => [[68,69]]
  | 4 => [[95,109]]
  | 5 => [[108,124]]
  | 6 => [[96,110]]
  | 7 => [[97,111]]
  | _ => []
theorem row67Fresh : Fresh 196 [67] (outside 196 domain) 53 := by
  unfold Fresh
  decide +kernel
private theorem row67Colors : Disjoint [67] (53 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row67DomainsFresh : ∀ i ∈ List.range 8, ∀ x ∈ row67Domains i,
    Fresh 196 [67] (53 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row67Disjoint : DomainsDisjoint 8 row67Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row67Shapes : ∀ i ∈ List.range 8, GuardOK (row67Domains i) (row67Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row67Covers : ProductCovers guards (53 :: outside 196 domain) 8 row67Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row67Components : ∀ i ∈ List.range 8,
    ¬ BlackWins (row67Targets i) 196 [] (outside 196 (row67Domains i)) := by
  intro i hi
  have hiN : i < 8 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 41) (b := 55) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 68) (b := 69) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
theorem row67Defense : ¬ BlackWins guards 196 [67] (53 :: outside 196 domain) := by
  apply product_not_blackWins row67Colors row67DomainsFresh row67Disjoint
  · intro i hi g hg; exact (row67Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row67Shapes i hi)
  · exact row67Components
  · exact row67Covers


end Snaky.BreakerN32.C00
