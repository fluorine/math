import Snaky.BreakerN32RootBase

namespace Snaky.BreakerN32.C00
open Snaky.Breaker
private def row83Domains : Nat → List Nat
  | 0 => [27,41]
  | 1 => [52,53]
  | 2 => [67,81]
  | 3 => [40,54]
  | 4 => Snaky.BreakerN32.C12.domain
  | _ => []
private def row83Targets : Nat → List (List Nat)
  | 0 => [[27,41]]
  | 1 => [[52,53]]
  | 2 => [[67,81]]
  | 3 => [[40,54]]
  | 4 => Snaky.BreakerN32.C12.guards
  | _ => []
theorem row83Fresh : Fresh 196 [83] (outside 196 domain) 69 := by
  unfold Fresh
  decide +kernel
private theorem row83Colors : Disjoint [83] (69 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row83DomainsFresh : ∀ i ∈ List.range 5, ∀ x ∈ row83Domains i,
    Fresh 196 [83] (69 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row83Disjoint : DomainsDisjoint 5 row83Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row83Shapes : ∀ i ∈ List.range 5, GuardOK (row83Domains i) (row83Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row83Covers : ProductCovers guards (69 :: outside 196 domain) 5 row83Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row83Components : ∀ i ∈ List.range 5,
    ¬ BlackWins (row83Targets i) 196 [] (outside 196 (row83Domains i)) := by
  intro i hi
  have hiN : i < 5 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 27) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 52) (b := 53) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 67) (b := 81) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 40) (b := 54) (by decide) (by decide) (by decide)
  · exact Snaky.BreakerN32.C12.defense
theorem row83Defense : ¬ BlackWins guards 196 [83] (69 :: outside 196 domain) := by
  apply product_not_blackWins row83Colors row83DomainsFresh row83Disjoint
  · intro i hi g hg; exact (row83Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row83Shapes i hi)
  · exact row83Components
  · exact row83Covers


end Snaky.BreakerN32.C00
