import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row108Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => [96,109]
  | 6 => [123,124]
  | 7 => [110,125]
  | 8 => [97,111]
  | _ => []
private def row108Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => [[96,109]]
  | 6 => [[123,124]]
  | 7 => [[110,125]]
  | 8 => [[97,111]]
  | _ => []
theorem row108Fresh : Fresh 196 [108] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row108Colors : Disjoint [108] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row108DomainsFresh : ∀ i ∈ List.range 9, ∀ x ∈ row108Domains i,
    Fresh 196 [108] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row108Disjoint : DomainsDisjoint 9 row108Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row108Shapes : ∀ i ∈ List.range 9, GuardOK (row108Domains i) (row108Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row108Covers : ProductCovers guards (68 :: outside 196 domain) 9 row108Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row108Components : ∀ i ∈ List.range 9,
    ¬ BlackWins (row108Targets i) 196 [] (outside 196 (row108Domains i)) := by
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
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
theorem row108Defense : ¬ BlackWins guards 196 [108] (68 :: outside 196 domain) := by
  apply product_not_blackWins row108Colors row108DomainsFresh row108Disjoint
  · intro i hi g hg; exact (row108Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row108Shapes i hi)
  · exact row108Components
  · exact row108Covers


end Snaky.BreakerN32.C00
