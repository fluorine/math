import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row96Domains : Nat → List Nat
  | 0 => [26,54]
  | 1 => [27,41]
  | 2 => [52,53]
  | 3 => [67,81]
  | 4 => [69,83]
  | 5 => Snaky.BreakerN32.C01.domain
  | _ => []
private def row96Targets : Nat → List (List Nat)
  | 0 => [[26,54]]
  | 1 => [[27,41]]
  | 2 => [[52,53]]
  | 3 => [[67,81]]
  | 4 => [[69,83]]
  | 5 => Snaky.BreakerN32.C01.guards
  | _ => []
theorem row96Fresh : Fresh 196 [96] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row96Colors : Disjoint [96] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row96DomainsFresh : ∀ i ∈ List.range 6, ∀ x ∈ row96Domains i,
    Fresh 196 [96] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row96Disjoint : DomainsDisjoint 6 row96Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row96Shapes : ∀ i ∈ List.range 6, GuardOK (row96Domains i) (row96Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row96Covers : ProductCovers guards (68 :: outside 196 domain) 6 row96Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row96Components : ∀ i ∈ List.range 6,
    ¬ BlackWins (row96Targets i) 196 [] (outside 196 (row96Domains i)) := by
  intro i hi
  have hiN : i < 6 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 26) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact Snaky.BreakerN32.C01.defense
theorem row96Defense : ¬ BlackWins guards 196 [96] (68 :: outside 196 domain) := by
  apply product_not_blackWins row96Colors row96DomainsFresh row96Disjoint
  · intro i hi g hg; exact (row96Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row96Shapes i hi)
  · exact row96Components
  · exact row96Covers


end Snaky.BreakerN32.C00
