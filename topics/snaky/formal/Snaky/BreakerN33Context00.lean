import Snaky.BreakerRounds
import Snaky.BreakerN33Context01

namespace Snaky.BreakerN33.C00
open Snaky.Breaker
def domain : List Nat := [95,97,108,109,110,111,123,124,125,139]
def guards : List (List Nat) := [[95,108,109],[95,109,123],[97,108,109,110],[97,111,125,139],[108,109,110,124,125],[108,109,123,124],[109,110,123],[110,111,125,139],[110,123,124],[110,124,125,139]]
theorem shape : GuardOK domain guards := by
  unfold GuardOK
  decide +kernel

private def row95Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [125,139]
  | _ => []
private def row95Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row95Fresh : Fresh 196 [95] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row95Colors : Disjoint [95] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row95DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row95Domains i,
    Fresh 196 [95] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row95Disjoint : DomainsDisjoint 2 row95Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row95Shapes : ∀ i ∈ List.range 2, GuardOK (row95Domains i) (row95Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row95Covers : ProductCovers guards (109 :: outside 196 domain) 2 row95Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row95Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row95Targets i) 196 [] (outside 196 (row95Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row95Defense : ¬ BlackWins guards 196 [95] (109 :: outside 196 domain) := by
  apply product_not_blackWins row95Colors row95DomainsFresh row95Disjoint
  · intro i hi g hg; exact (row95Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row95Shapes i hi)
  · exact row95Components
  · exact row95Covers

private def row97Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [125,139]
  | _ => []
private def row97Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row97Fresh : Fresh 196 [97] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row97Colors : Disjoint [97] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row97DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row97Domains i,
    Fresh 196 [97] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row97Disjoint : DomainsDisjoint 2 row97Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row97Shapes : ∀ i ∈ List.range 2, GuardOK (row97Domains i) (row97Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row97Covers : ProductCovers guards (109 :: outside 196 domain) 2 row97Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row97Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row97Targets i) 196 [] (outside 196 (row97Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row97Defense : ¬ BlackWins guards 196 [97] (109 :: outside 196 domain) := by
  apply product_not_blackWins row97Colors row97DomainsFresh row97Disjoint
  · intro i hi g hg; exact (row97Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row97Shapes i hi)
  · exact row97Components
  · exact row97Covers

private def row108Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [125,139]
  | _ => []
private def row108Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row108Fresh : Fresh 196 [108] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row108Colors : Disjoint [108] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row108DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row108Domains i,
    Fresh 196 [108] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row108Disjoint : DomainsDisjoint 2 row108Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row108Shapes : ∀ i ∈ List.range 2, GuardOK (row108Domains i) (row108Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row108Covers : ProductCovers guards (109 :: outside 196 domain) 2 row108Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row108Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row108Targets i) 196 [] (outside 196 (row108Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row108Defense : ¬ BlackWins guards 196 [108] (109 :: outside 196 domain) := by
  apply product_not_blackWins row108Colors row108DomainsFresh row108Disjoint
  · intro i hi g hg; exact (row108Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row108Shapes i hi)
  · exact row108Components
  · exact row108Covers

private def row109Domains : Nat → List Nat
  | 0 => Snaky.BreakerN33.C01.domain
  | _ => []
private def row109Targets : Nat → List (List Nat)
  | 0 => Snaky.BreakerN33.C01.guards
  | _ => []
private theorem row109Fresh : Fresh 196 [109] (outside 196 domain) 95 := by
  unfold Fresh
  decide +kernel
private theorem row109Colors : Disjoint [109] (95 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row109DomainsFresh : ∀ i ∈ List.range 1, ∀ x ∈ row109Domains i,
    Fresh 196 [109] (95 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row109Disjoint : DomainsDisjoint 1 row109Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row109Shapes : ∀ i ∈ List.range 1, GuardOK (row109Domains i) (row109Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row109Covers : ProductCovers guards (95 :: outside 196 domain) 1 row109Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row109Components : ∀ i ∈ List.range 1,
    ¬ BlackWins (row109Targets i) 196 [] (outside 196 (row109Domains i)) := by
  intro i hi
  have hiN : i < 1 := List.mem_range.mp hi
  have cases : i = 0 := by omega
  rcases cases with rfl
  · exact Snaky.BreakerN33.C01.defense
private theorem row109Defense : ¬ BlackWins guards 196 [109] (95 :: outside 196 domain) := by
  apply product_not_blackWins row109Colors row109DomainsFresh row109Disjoint
  · intro i hi g hg; exact (row109Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row109Shapes i hi)
  · exact row109Components
  · exact row109Covers

private def row110Domains : Nat → List Nat
  | 0 => [123,124]
  | 1 => [125,139]
  | _ => []
private def row110Targets : Nat → List (List Nat)
  | 0 => [[123,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row110Fresh : Fresh 196 [110] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row110Colors : Disjoint [110] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row110DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row110Domains i,
    Fresh 196 [110] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row110Disjoint : DomainsDisjoint 2 row110Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row110Shapes : ∀ i ∈ List.range 2, GuardOK (row110Domains i) (row110Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row110Covers : ProductCovers guards (109 :: outside 196 domain) 2 row110Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row110Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row110Targets i) 196 [] (outside 196 (row110Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 123) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row110Defense : ¬ BlackWins guards 196 [110] (109 :: outside 196 domain) := by
  apply product_not_blackWins row110Colors row110DomainsFresh row110Disjoint
  · intro i hi g hg; exact (row110Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row110Shapes i hi)
  · exact row110Components
  · exact row110Covers

private def row111Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [125,139]
  | _ => []
private def row111Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row111Fresh : Fresh 196 [111] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row111Colors : Disjoint [111] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row111DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row111Domains i,
    Fresh 196 [111] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row111Disjoint : DomainsDisjoint 2 row111Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row111Shapes : ∀ i ∈ List.range 2, GuardOK (row111Domains i) (row111Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row111Covers : ProductCovers guards (109 :: outside 196 domain) 2 row111Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row111Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row111Targets i) 196 [] (outside 196 (row111Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row111Defense : ¬ BlackWins guards 196 [111] (109 :: outside 196 domain) := by
  apply product_not_blackWins row111Colors row111DomainsFresh row111Disjoint
  · intro i hi g hg; exact (row111Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row111Shapes i hi)
  · exact row111Components
  · exact row111Covers

private def row123Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [125,139]
  | _ => []
private def row123Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[125,139]]
  | _ => []
private theorem row123Fresh : Fresh 196 [123] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row123Colors : Disjoint [123] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row123DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row123Domains i,
    Fresh 196 [123] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row123Disjoint : DomainsDisjoint 2 row123Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row123Shapes : ∀ i ∈ List.range 2, GuardOK (row123Domains i) (row123Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row123Covers : ProductCovers guards (109 :: outside 196 domain) 2 row123Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row123Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row123Targets i) 196 [] (outside 196 (row123Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row123Defense : ¬ BlackWins guards 196 [123] (109 :: outside 196 domain) := by
  apply product_not_blackWins row123Colors row123DomainsFresh row123Disjoint
  · intro i hi g hg; exact (row123Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row123Shapes i hi)
  · exact row123Components
  · exact row123Covers

private def row124Domains : Nat → List Nat
  | 0 => [110,123]
  | 1 => [125,139]
  | _ => []
private def row124Targets : Nat → List (List Nat)
  | 0 => [[110,123]]
  | 1 => [[125,139]]
  | _ => []
private theorem row124Fresh : Fresh 196 [124] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row124Colors : Disjoint [124] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row124DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row124Domains i,
    Fresh 196 [124] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row124Disjoint : DomainsDisjoint 2 row124Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row124Shapes : ∀ i ∈ List.range 2, GuardOK (row124Domains i) (row124Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row124Covers : ProductCovers guards (109 :: outside 196 domain) 2 row124Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row124Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row124Targets i) 196 [] (outside 196 (row124Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row124Defense : ¬ BlackWins guards 196 [124] (109 :: outside 196 domain) := by
  apply product_not_blackWins row124Colors row124DomainsFresh row124Disjoint
  · intro i hi g hg; exact (row124Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row124Shapes i hi)
  · exact row124Components
  · exact row124Covers

private def row125Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [111,139]
  | _ => []
private def row125Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[111,139]]
  | _ => []
private theorem row125Fresh : Fresh 196 [125] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row125Colors : Disjoint [125] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row125DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row125Domains i,
    Fresh 196 [125] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row125Disjoint : DomainsDisjoint 2 row125Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row125Shapes : ∀ i ∈ List.range 2, GuardOK (row125Domains i) (row125Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row125Covers : ProductCovers guards (109 :: outside 196 domain) 2 row125Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row125Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row125Targets i) 196 [] (outside 196 (row125Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
private theorem row125Defense : ¬ BlackWins guards 196 [125] (109 :: outside 196 domain) := by
  apply product_not_blackWins row125Colors row125DomainsFresh row125Disjoint
  · intro i hi g hg; exact (row125Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row125Shapes i hi)
  · exact row125Components
  · exact row125Covers

private def row139Domains : Nat → List Nat
  | 0 => [110,124]
  | 1 => [111,125]
  | _ => []
private def row139Targets : Nat → List (List Nat)
  | 0 => [[110,124]]
  | 1 => [[111,125]]
  | _ => []
private theorem row139Fresh : Fresh 196 [139] (outside 196 domain) 109 := by
  unfold Fresh
  decide +kernel
private theorem row139Colors : Disjoint [139] (109 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row139DomainsFresh : ∀ i ∈ List.range 2, ∀ x ∈ row139Domains i,
    Fresh 196 [139] (109 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row139Disjoint : DomainsDisjoint 2 row139Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row139Shapes : ∀ i ∈ List.range 2, GuardOK (row139Domains i) (row139Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row139Covers : ProductCovers guards (109 :: outside 196 domain) 2 row139Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row139Components : ∀ i ∈ List.range 2,
    ¬ BlackWins (row139Targets i) 196 [] (outside 196 (row139Domains i)) := by
  intro i hi
  have hiN : i < 2 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 125) (by decide) (by decide) (by decide)
private theorem row139Defense : ¬ BlackWins guards 196 [139] (109 :: outside 196 domain) := by
  apply product_not_blackWins row139Colors row139DomainsFresh row139Disjoint
  · intro i hi g hg; exact (row139Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row139Shapes i hi)
  · exact row139Components
  · exact row139Covers

theorem defense : ¬ BlackWins guards 196 [] (outside 196 domain) := by
  apply local_round_not_blackWins shape
  intro u hu
  have cases : u = 95 ∨ u = 97 ∨ u = 108 ∨ u = 109 ∨ u = 110 ∨ u = 111 ∨ u = 123 ∨ u = 124 ∨ u = 125 ∨ u = 139 := by
    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨109, row95Fresh, row95Defense⟩
  · exact ⟨109, row97Fresh, row97Defense⟩
  · exact ⟨109, row108Fresh, row108Defense⟩
  · exact ⟨95, row109Fresh, row109Defense⟩
  · exact ⟨109, row110Fresh, row110Defense⟩
  · exact ⟨109, row111Fresh, row111Defense⟩
  · exact ⟨109, row123Fresh, row123Defense⟩
  · exact ⟨109, row124Fresh, row124Defense⟩
  · exact ⟨109, row125Fresh, row125Defense⟩
  · exact ⟨109, row139Fresh, row139Defense⟩

end Snaky.BreakerN33.C00
