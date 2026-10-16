import Snaky.BreakerRounds
import Snaky.BreakerN32Context05
import Snaky.BreakerN32Context07

namespace Snaky.BreakerN32.C04
open Snaky.Breaker
def domain : List Nat := [68,95,96,97,108,109,110,111,123,124,125,139]
def guards : List (List Nat) := [[68,95,109,123],[68,96],[68,97,111,125],[95,96,108,109],[95,96,109,123],[96,97,108,109,110],[96,97,111,125,139],[96,109,110,123],[96,110,111,125,139],[96,110,123,124],[96,110,124,125,139],[108,109,110,124,125],[108,109,123,124]]
theorem shape : GuardOK domain guards := by
  unfold GuardOK
  decide +kernel

private def row68Domains : Nat → List Nat
  | 0 => [108,109]
  | 1 => [95,123]
  | 2 => [97,125]
  | _ => []
private def row68Targets : Nat → List (List Nat)
  | 0 => [[108,109]]
  | 1 => [[95,123]]
  | 2 => [[97,125]]
  | _ => []
private theorem row68Fresh : Fresh 196 [68] (outside 196 domain) 96 := by
  unfold Fresh
  decide +kernel
private theorem row68Colors : Disjoint [68] (96 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row68DomainsFresh : ∀ i ∈ List.range 3, ∀ x ∈ row68Domains i,
    Fresh 196 [68] (96 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row68Disjoint : DomainsDisjoint 3 row68Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row68Shapes : ∀ i ∈ List.range 3, GuardOK (row68Domains i) (row68Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row68Covers : ProductCovers guards (96 :: outside 196 domain) 3 row68Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row68Components : ∀ i ∈ List.range 3,
    ¬ BlackWins (row68Targets i) 196 [] (outside 196 (row68Domains i)) := by
  intro i hi
  have hiN : i < 3 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 125) (by decide) (by decide) (by decide)
private theorem row68Defense : ¬ BlackWins guards 196 [68] (96 :: outside 196 domain) := by
  apply product_not_blackWins row68Colors row68DomainsFresh row68Disjoint
  · intro i hi g hg; exact (row68Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row68Shapes i hi)
  · exact row68Components
  · exact row68Covers

private def row95Domains : Nat → List Nat
  | 0 => [108,109]
  | 1 => [110,124]
  | 2 => [111,139]
  | 3 => [96,123]
  | _ => []
private def row95Targets : Nat → List (List Nat)
  | 0 => [[108,109]]
  | 1 => [[110,124]]
  | 2 => [[111,139]]
  | 3 => [[96,123]]
  | _ => []
private theorem row95Fresh : Fresh 196 [95] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row95Colors : Disjoint [95] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row95DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row95Domains i,
    Fresh 196 [95] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row95Disjoint : DomainsDisjoint 4 row95Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row95Shapes : ∀ i ∈ List.range 4, GuardOK (row95Domains i) (row95Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row95Covers : ProductCovers guards (68 :: outside 196 domain) 4 row95Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row95Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row95Targets i) 196 [] (outside 196 (row95Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
private theorem row95Defense : ¬ BlackWins guards 196 [95] (68 :: outside 196 domain) := by
  apply product_not_blackWins row95Colors row95DomainsFresh row95Disjoint
  · intro i hi g hg; exact (row95Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row95Shapes i hi)
  · exact row95Components
  · exact row95Covers

private def row96Domains : Nat → List Nat
  | 0 => Snaky.BreakerN32.C05.domain
  | _ => []
private def row96Targets : Nat → List (List Nat)
  | 0 => Snaky.BreakerN32.C05.guards
  | _ => []
private theorem row96Fresh : Fresh 196 [96] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row96Colors : Disjoint [96] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row96DomainsFresh : ∀ i ∈ List.range 1, ∀ x ∈ row96Domains i,
    Fresh 196 [96] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row96Disjoint : DomainsDisjoint 1 row96Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row96Shapes : ∀ i ∈ List.range 1, GuardOK (row96Domains i) (row96Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row96Covers : ProductCovers guards (68 :: outside 196 domain) 1 row96Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row96Components : ∀ i ∈ List.range 1,
    ¬ BlackWins (row96Targets i) 196 [] (outside 196 (row96Domains i)) := by
  intro i hi
  have hiN : i < 1 := List.mem_range.mp hi
  have cases : i = 0 := by omega
  rcases cases with rfl
  · exact Snaky.BreakerN32.C05.defense
private theorem row96Defense : ¬ BlackWins guards 196 [96] (68 :: outside 196 domain) := by
  apply product_not_blackWins row96Colors row96DomainsFresh row96Disjoint
  · intro i hi g hg; exact (row96Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row96Shapes i hi)
  · exact row96Components
  · exact row96Covers

private def row97Domains : Nat → List Nat
  | 0 => [108,109]
  | 1 => [110,124]
  | 2 => [111,139]
  | 3 => [96,123]
  | _ => []
private def row97Targets : Nat → List (List Nat)
  | 0 => [[108,109]]
  | 1 => [[110,124]]
  | 2 => [[111,139]]
  | 3 => [[96,123]]
  | _ => []
private theorem row97Fresh : Fresh 196 [97] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row97Colors : Disjoint [97] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row97DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row97Domains i,
    Fresh 196 [97] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row97Disjoint : DomainsDisjoint 4 row97Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row97Shapes : ∀ i ∈ List.range 4, GuardOK (row97Domains i) (row97Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row97Covers : ProductCovers guards (68 :: outside 196 domain) 4 row97Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row97Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row97Targets i) 196 [] (outside 196 (row97Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
private theorem row97Defense : ¬ BlackWins guards 196 [97] (68 :: outside 196 domain) := by
  apply product_not_blackWins row97Colors row97DomainsFresh row97Disjoint
  · intro i hi g hg; exact (row97Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row97Shapes i hi)
  · exact row97Components
  · exact row97Covers

private def row108Domains : Nat → List Nat
  | 0 => [96,109]
  | 1 => [123,124]
  | 2 => [110,125]
  | 3 => [97,111]
  | _ => []
private def row108Targets : Nat → List (List Nat)
  | 0 => [[96,109]]
  | 1 => [[123,124]]
  | 2 => [[110,125]]
  | 3 => [[97,111]]
  | _ => []
private theorem row108Fresh : Fresh 196 [108] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row108Colors : Disjoint [108] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row108DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row108Domains i,
    Fresh 196 [108] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row108Disjoint : DomainsDisjoint 4 row108Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row108Shapes : ∀ i ∈ List.range 4, GuardOK (row108Domains i) (row108Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row108Covers : ProductCovers guards (68 :: outside 196 domain) 4 row108Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row108Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row108Targets i) 196 [] (outside 196 (row108Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 123) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
private theorem row108Defense : ¬ BlackWins guards 196 [108] (68 :: outside 196 domain) := by
  apply product_not_blackWins row108Colors row108DomainsFresh row108Disjoint
  · intro i hi g hg; exact (row108Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row108Shapes i hi)
  · exact row108Components
  · exact row108Covers

private def row109Domains : Nat → List Nat
  | 0 => Snaky.BreakerN32.C07.domain
  | _ => []
private def row109Targets : Nat → List (List Nat)
  | 0 => Snaky.BreakerN32.C07.guards
  | _ => []
private theorem row109Fresh : Fresh 196 [109] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row109Colors : Disjoint [109] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row109DomainsFresh : ∀ i ∈ List.range 1, ∀ x ∈ row109Domains i,
    Fresh 196 [109] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row109Disjoint : DomainsDisjoint 1 row109Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row109Shapes : ∀ i ∈ List.range 1, GuardOK (row109Domains i) (row109Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row109Covers : ProductCovers guards (68 :: outside 196 domain) 1 row109Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row109Components : ∀ i ∈ List.range 1,
    ¬ BlackWins (row109Targets i) 196 [] (outside 196 (row109Domains i)) := by
  intro i hi
  have hiN : i < 1 := List.mem_range.mp hi
  have cases : i = 0 := by omega
  rcases cases with rfl
  · exact Snaky.BreakerN32.C07.defense
private theorem row109Defense : ¬ BlackWins guards 196 [109] (68 :: outside 196 domain) := by
  apply product_not_blackWins row109Colors row109DomainsFresh row109Disjoint
  · intro i hi g hg; exact (row109Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row109Shapes i hi)
  · exact row109Components
  · exact row109Covers

private def row110Domains : Nat → List Nat
  | 0 => [108,109]
  | 1 => [96,123]
  | 2 => [124,125]
  | 3 => [111,139]
  | _ => []
private def row110Targets : Nat → List (List Nat)
  | 0 => [[108,109]]
  | 1 => [[96,123]]
  | 2 => [[124,125]]
  | 3 => [[111,139]]
  | _ => []
private theorem row110Fresh : Fresh 196 [110] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row110Colors : Disjoint [110] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row110DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row110Domains i,
    Fresh 196 [110] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row110Disjoint : DomainsDisjoint 4 row110Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row110Shapes : ∀ i ∈ List.range 4, GuardOK (row110Domains i) (row110Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row110Covers : ProductCovers guards (68 :: outside 196 domain) 4 row110Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row110Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row110Targets i) 196 [] (outside 196 (row110Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 124) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
private theorem row110Defense : ¬ BlackWins guards 196 [110] (68 :: outside 196 domain) := by
  apply product_not_blackWins row110Colors row110DomainsFresh row110Disjoint
  · intro i hi g hg; exact (row110Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row110Shapes i hi)
  · exact row110Components
  · exact row110Covers

private def row111Domains : Nat → List Nat
  | 0 => [96,109]
  | 1 => [123,124]
  | 2 => [108,110]
  | 3 => [125,139]
  | _ => []
private def row111Targets : Nat → List (List Nat)
  | 0 => [[96,109]]
  | 1 => [[123,124]]
  | 2 => [[108,110]]
  | 3 => [[125,139]]
  | _ => []
private theorem row111Fresh : Fresh 196 [111] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row111Colors : Disjoint [111] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row111DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row111Domains i,
    Fresh 196 [111] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row111Disjoint : DomainsDisjoint 4 row111Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row111Shapes : ∀ i ∈ List.range 4, GuardOK (row111Domains i) (row111Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row111Covers : ProductCovers guards (68 :: outside 196 domain) 4 row111Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row111Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row111Targets i) 196 [] (outside 196 (row111Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 123) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 125) (b := 139) (by decide) (by decide) (by decide)
private theorem row111Defense : ¬ BlackWins guards 196 [111] (68 :: outside 196 domain) := by
  apply product_not_blackWins row111Colors row111DomainsFresh row111Disjoint
  · intro i hi g hg; exact (row111Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row111Shapes i hi)
  · exact row111Components
  · exact row111Covers

private def row123Domains : Nat → List Nat
  | 0 => [96,110]
  | 1 => [95,109]
  | 2 => [108,124]
  | 3 => [111,139]
  | _ => []
private def row123Targets : Nat → List (List Nat)
  | 0 => [[96,110]]
  | 1 => [[95,109]]
  | 2 => [[108,124]]
  | 3 => [[111,139]]
  | _ => []
private theorem row123Fresh : Fresh 196 [123] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row123Colors : Disjoint [123] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row123DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row123Domains i,
    Fresh 196 [123] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row123Disjoint : DomainsDisjoint 4 row123Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row123Shapes : ∀ i ∈ List.range 4, GuardOK (row123Domains i) (row123Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row123Covers : ProductCovers guards (68 :: outside 196 domain) 4 row123Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row123Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row123Targets i) 196 [] (outside 196 (row123Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
private theorem row123Defense : ¬ BlackWins guards 196 [123] (68 :: outside 196 domain) := by
  apply product_not_blackWins row123Colors row123DomainsFresh row123Disjoint
  · intro i hi g hg; exact (row123Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row123Shapes i hi)
  · exact row123Components
  · exact row123Covers

private def row124Domains : Nat → List Nat
  | 0 => [96,110]
  | 1 => [108,109]
  | 2 => [95,123]
  | 3 => [111,139]
  | _ => []
private def row124Targets : Nat → List (List Nat)
  | 0 => [[96,110]]
  | 1 => [[108,109]]
  | 2 => [[95,123]]
  | 3 => [[111,139]]
  | _ => []
private theorem row124Fresh : Fresh 196 [124] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row124Colors : Disjoint [124] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row124DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row124Domains i,
    Fresh 196 [124] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row124Disjoint : DomainsDisjoint 4 row124Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row124Shapes : ∀ i ∈ List.range 4, GuardOK (row124Domains i) (row124Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row124Covers : ProductCovers guards (68 :: outside 196 domain) 4 row124Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row124Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row124Targets i) 196 [] (outside 196 (row124Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 110) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 95) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
private theorem row124Defense : ¬ BlackWins guards 196 [124] (68 :: outside 196 domain) := by
  apply product_not_blackWins row124Colors row124DomainsFresh row124Disjoint
  · intro i hi g hg; exact (row124Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row124Shapes i hi)
  · exact row124Components
  · exact row124Covers

private def row125Domains : Nat → List Nat
  | 0 => [108,109]
  | 1 => [110,124]
  | 2 => [111,139]
  | 3 => [96,123]
  | _ => []
private def row125Targets : Nat → List (List Nat)
  | 0 => [[108,109]]
  | 1 => [[110,124]]
  | 2 => [[111,139]]
  | 3 => [[96,123]]
  | _ => []
private theorem row125Fresh : Fresh 196 [125] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row125Colors : Disjoint [125] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row125DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row125Domains i,
    Fresh 196 [125] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row125Disjoint : DomainsDisjoint 4 row125Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row125Shapes : ∀ i ∈ List.range 4, GuardOK (row125Domains i) (row125Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row125Covers : ProductCovers guards (68 :: outside 196 domain) 4 row125Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row125Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row125Targets i) 196 [] (outside 196 (row125Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 124) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 111) (b := 139) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
private theorem row125Defense : ¬ BlackWins guards 196 [125] (68 :: outside 196 domain) := by
  apply product_not_blackWins row125Colors row125DomainsFresh row125Disjoint
  · intro i hi g hg; exact (row125Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row125Shapes i hi)
  · exact row125Components
  · exact row125Covers

private def row139Domains : Nat → List Nat
  | 0 => [96,123]
  | 1 => [108,109]
  | 2 => [110,125]
  | 3 => [97,111]
  | _ => []
private def row139Targets : Nat → List (List Nat)
  | 0 => [[96,123]]
  | 1 => [[108,109]]
  | 2 => [[110,125]]
  | 3 => [[97,111]]
  | _ => []
private theorem row139Fresh : Fresh 196 [139] (outside 196 domain) 68 := by
  unfold Fresh
  decide +kernel
private theorem row139Colors : Disjoint [139] (68 :: outside 196 domain) := by
  unfold Disjoint
  decide +kernel
private theorem row139DomainsFresh : ∀ i ∈ List.range 4, ∀ x ∈ row139Domains i,
    Fresh 196 [139] (68 :: outside 196 domain) x := by
  unfold Fresh
  decide +kernel
private theorem row139Disjoint : DomainsDisjoint 4 row139Domains := by
  unfold DomainsDisjoint
  decide +kernel
private theorem row139Shapes : ∀ i ∈ List.range 4, GuardOK (row139Domains i) (row139Targets i) := by
  unfold GuardOK
  decide +kernel
private theorem row139Covers : ProductCovers guards (68 :: outside 196 domain) 4 row139Targets := by
  unfold ProductCovers
  decide +kernel
private theorem row139Components : ∀ i ∈ List.range 4,
    ¬ BlackWins (row139Targets i) 196 [] (outside 196 (row139Domains i)) := by
  intro i hi
  have hiN : i < 4 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 96) (b := 123) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 108) (b := 109) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 110) (b := 125) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 97) (b := 111) (by decide) (by decide) (by decide)
private theorem row139Defense : ¬ BlackWins guards 196 [139] (68 :: outside 196 domain) := by
  apply product_not_blackWins row139Colors row139DomainsFresh row139Disjoint
  · intro i hi g hg; exact (row139Shapes i hi g hg).1
  · intro i hi; exact guard_noComplete_empty (row139Shapes i hi)
  · exact row139Components
  · exact row139Covers

theorem defense : ¬ BlackWins guards 196 [] (outside 196 domain) := by
  apply local_round_not_blackWins shape
  intro u hu
  have cases : u = 68 ∨ u = 95 ∨ u = 96 ∨ u = 97 ∨ u = 108 ∨ u = 109 ∨ u = 110 ∨ u = 111 ∨ u = 123 ∨ u = 124 ∨ u = 125 ∨ u = 139 := by
    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨96, row68Fresh, row68Defense⟩
  · exact ⟨68, row95Fresh, row95Defense⟩
  · exact ⟨68, row96Fresh, row96Defense⟩
  · exact ⟨68, row97Fresh, row97Defense⟩
  · exact ⟨68, row108Fresh, row108Defense⟩
  · exact ⟨68, row109Fresh, row109Defense⟩
  · exact ⟨68, row110Fresh, row110Defense⟩
  · exact ⟨68, row111Fresh, row111Defense⟩
  · exact ⟨68, row123Fresh, row123Defense⟩
  · exact ⟨68, row124Fresh, row124Defense⟩
  · exact ⟨68, row125Fresh, row125Defense⟩
  · exact ⟨68, row139Fresh, row139Defense⟩

end Snaky.BreakerN32.C04
