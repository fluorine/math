import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row53Domains : Nat → List Nat
  | 0 => [27,41]
  | 1 => [67,81]
  | 2 => [69,83]
  | 3 => [40,54]
  | 4 => Snaky.BreakerN32.C08.domain
  | _ => []
private def row53Targets : Nat → List (List Nat)
  | 0 => [[27,41]]
  | 1 => [[67,81]]
  | 2 => [[69,83]]
  | 3 => [[40,54]]
  | 4 => Snaky.BreakerN32.C08.guards
  | _ => []
theorem row53Fresh : Fresh 196 [53] (outside 196 domain) 52 := by
  unfold Fresh
  decide +kernel
private theorem row53Colors : Disjoint [53] (52 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row53DomainsFresh : ∀ i ∈ List.range 5, ∀ x ∈ row53Domains i,
    Fresh 196 [53] (52 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row53Disjoint : DomainsDisjoint 5 row53Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row53Shapes : ∀ i ∈ List.range 5, GuardOK (row53Domains i) (row53Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row53Covers : ProductCovers guards (52 :: outside 196 domain) 5 row53Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row53Components : ∀ i ∈ List.range 5,
    ¬ BlackWins (row53Targets i) 196 [] (outside 196 (row53Domains i)) := by
  intro i hi
  have hiN : i < 5 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 69) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact Snaky.BreakerN32.C08.defense
theorem row53Defense : ¬ BlackWins guards 196 [53] (52 :: outside 196 domain) := by
  apply product_not_blackWins row53Colors row53DomainsFresh row53Disjoint
  · intro i hi g hg; exact (row53Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row53Shapes i hi)
  · exact row53Components
  · exact row53Covers


end Snaky.BreakerN32.C00
