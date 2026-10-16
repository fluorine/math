import Snaky.BreakerSwitch

/-! Untrusted L_cap34+34 literals, generated from the pinned accepted report.
Totalization pairs only unused fresh cells. The proof uses no report result. -/
namespace Snaky.BreakerLCap
open Snaky.Breaker
def maker : List Nat := [48,49,51,60,61,62,66,75,76,77,79,82,88,90,93,96,102,103,104,105,106,107,109,116,121,129,130,133,135,136,137,147,148,149]
def breaker : List Nat := [25,34,35,47,50,59,63,65,68,74,78,80,87,89,91,92,94,95,101,115,117,118,119,120,122,131,134,138,143,144,146,150,162,164]
def reserved : List Nat := [97,108,110,111,123,124,125,139]
def guards : List (List Nat) := [[97,108,110],[97,111,125,139],[108,110,124,125],[108,123,124],[110,111,125,139],[110,123],[110,123,124],[110,124,125,139]]
def outsidePairs : List (Nat × Nat) := [(0,14),(56,1),(2,4),(3,17),(5,6),(7,8),(9,37),(20,10),(11,12),(15,16),(18,19),(21,22),(23,24),(26,54),(27,41),(28,45),(70,29),(30,31),(32,46),(38,39),(42,85),(43,44),(52,53),(57,71),(58,72),(67,81),(69,83),(84,98),(86,100),(99,113),(112,126),(114,142),(127,128),(140,168),(141,155),(151,165),(152,166),(153,167),(156,170),(157,158),(159,160),(188,161),(163,177),(171,172),(175,176),(178,179),(191,180),(194,181),(185,186),(189,190),(192,193),(13,33),(36,40),(55,64),(73,132),(145,154),(169,173),(174,182),(183,184),(187,195)]
def outsideMate := mateOfPairs outsidePairs
def reply : Nat → Nat
  | 97 => 123
  | 108 => 123
  | 110 => 123
  | 111 => 123
  | 123 => 110
  | 124 => 123
  | 125 => 123
  | 139 => 123
  | u => u
def localPairs : Nat → List (Nat × Nat)
  | 97 => [(108,110),(124,125),(111,139)]
  | 108 => [(110,97),(124,125),(111,139)]
  | 110 => [(108,97),(124,125),(111,139)]
  | 111 => [(108,110),(125,139),(97,124)]
  | 123 => [(108,124),(111,139),(97,125)]
  | 124 => [(108,110),(125,139),(97,111)]
  | 125 => [(108,97),(110,124),(111,139)]
  | 139 => [(108,97),(110,124),(111,125)]
  | _ => []
def localMate (u : Nat) := mateOfPairs (localPairs u)
theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel
theorem reserved_fresh : ∀ x ∈ reserved, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem block0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block100 : ∀ x ∈ List.range 120, 100 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block120 : ∀ x ∈ List.range 140, 120 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block140 : ∀ x ∈ List.range 160, 140 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block160 : ∀ x ∈ List.range 180, 160 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block180 : ∀ x ∈ List.range 196, 180 ≤ x →
    x ∉ maker → x ∉ breaker → x ∉ reserved → Fresh 196 maker breaker (outsideMate x) ∧ outsideMate x ∉ reserved ∧ outsideMate x ≠ x ∧ outsideMate (outsideMate x) = x := by
  unfold Fresh
  decide +kernel

theorem exterior_matching : OuterOK 196 maker breaker reserved outsideMate := by
  intro x hx hm hb hr
  have hx196 : x < 196 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact block0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact block20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact block40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact block60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  by_cases h100 : x < 100
  · exact block80 x (List.mem_range.mpr h100) (by omega) hm hb hr
  by_cases h120 : x < 120
  · exact block100 x (List.mem_range.mpr h120) (by omega) hm hb hr
  by_cases h140 : x < 140
  · exact block120 x (List.mem_range.mpr h140) (by omega) hm hb hr
  by_cases h160 : x < 160
  · exact block140 x (List.mem_range.mpr h160) (by omega) hm hb hr
  by_cases h180 : x < 180
  · exact block160 x (List.mem_range.mpr h180) (by omega) hm hb hr
  exact block180 x (List.mem_range.mpr hx196) (by omega) hm hb hr
theorem guard_shape : GuardOK reserved guards := by
  unfold GuardOK
  decide +kernel
theorem switch_rows : SwitchOK reserved guards reply localMate := by
  unfold SwitchOK
  decide +kernel
end Snaky.BreakerLCap
