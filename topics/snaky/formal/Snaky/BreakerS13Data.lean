import Snaky.BreakerPairing

/-! Exact conditional physical endpoint from `verification/browser-eighteenth-full-pairing05-01.pairing.json`.
Generated literals are not axioms; all finite hypotheses and target coverage
are independently reduced in Lean's kernel. -/
namespace Snaky.BreakerS13
open Snaky.Breaker
def maker : List Nat := [11,21,31,32,37,44,45,46,47,57,67,75,84]
def breaker : List Nat := [1,14,24,34,36,38,43,55,56,58,74,77,94]
def pairs : List (Nat × Nat) := [(0,10),(2,12),(3,13),(4,15),(5,6),(7,9),(8,17),(16,27),(18,28),(19,26),(25,35),(39,49),(40,50),(41,51),(42,52),(53,54),(59,69),(60,80),(61,81),(62,72),(63,64),(65,95),(66,76),(68,78),(70,71),(73,93),(82,83),(85,86),(88,89),(90,91),(96,97),(20,22),(23,29),(30,33),(48,79),(87,92),(98,99)]
def mate := mateOfPairs pairs
theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel
private theorem block0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker → x ∉ breaker → Fresh 100 maker breaker (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker → x ∉ breaker → Fresh 100 maker breaker (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker → x ∉ breaker → Fresh 100 maker breaker (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker → x ∉ breaker → Fresh 100 maker breaker (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x := by
  unfold Fresh
  decide +kernel

private theorem block80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker → x ∉ breaker → Fresh 100 maker breaker (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x := by
  unfold Fresh
  decide +kernel

theorem matching_ok : MatchingOK 100 maker breaker mate := by
  intro x hx hm hb
  have hx100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact block0 x (List.mem_range.mpr h20) (by omega) hm hb
  by_cases h40 : x < 40
  · exact block20 x (List.mem_range.mpr h40) (by omega) hm hb
  by_cases h60 : x < 60
  · exact block40 x (List.mem_range.mpr h60) (by omega) hm hb
  by_cases h80 : x < 80
  · exact block60 x (List.mem_range.mpr h80) (by omega) hm hb
  exact block80 x (List.mem_range.mpr hx100) (by omega) hm hb
end Snaky.BreakerS13
