import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row81Domains : Nat → List Nat
  | 0 => [27,41]
  | 1 => [52,53]
  | 2 => [69,83]
  | 3 => [40,54]
  | 4 => Snaky.BreakerN32.C04.domain
  | _ => []
private def row81Targets : Nat → List (List Nat)
  | 0 => [[27,41]]
  | 1 => [[52,53]]
  | 2 => [[69,83]]
  | 3 => [[40,54]]
  | 4 => Snaky.BreakerN32.C04.guards
  | _ => []
theorem row81Fresh : Fresh 196 [81] (outside 196 domain) 67 := by
  unfold Fresh
  decide +kernel
private theorem row81Colors : Disjoint [81] (67 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row81DomainsFresh : ∀ i ∈ List.range 5, ∀ x ∈ row81Domains i,
    Fresh 196 [81] (67 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row81Disjoint : DomainsDisjoint 5 row81Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row81Shapes : ∀ i ∈ List.range 5, GuardOK (row81Domains i) (row81Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row81Covers : ProductCovers guards (67 :: outside 196 domain) 5 row81Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row81Components : ∀ i ∈ List.range 5,
    ¬ BlackWins (row81Targets i) 196 [] (outside 196 (row81Domains i)) := by
  intro i hi
  have hiN : i < 5 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact Snaky.BreakerN32.C04.defense
theorem row81Defense : ¬ BlackWins guards 196 [81] (67 :: outside 196 domain) := by
  apply product_not_blackWins row81Colors row81DomainsFresh row81Disjoint
  · intro i hi g hg; exact (row81Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row81Shapes i hi)
  · exact row81Components
  · exact row81Covers


end Snaky.BreakerN32.C00
