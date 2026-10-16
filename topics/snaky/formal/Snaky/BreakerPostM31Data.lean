import Snaky.BreakerPairing

/-! Exact conditional physical endpoint from `verification/post-m31-joint-matching-result-01.pairing.json`.
Generated literals are not axioms; all finite hypotheses and target coverage
are independently reduced in Lean's kernel. -/
namespace Snaky.BreakerPostM31
open Snaky.Breaker
def maker : List Nat := [11,21,31,37,44,45,46,47,57,67,75,84]
def breaker : List Nat := [14,34,36,38,41,43,55,56,58,74,77,94]
def pairs : List (Nat × Nat) := [(1,30),(2,10),(3,13),(4,5),(6,19),(8,9),(12,22),(15,25),(16,26),(17,27),(18,28),(20,51),(23,24),(29,39),(32,42),(33,52),(40,50),(53,54),(59,69),(60,70),(61,80),(62,72),(63,64),(65,95),(66,76),(68,78),(71,81),(73,83),(79,89),(82,85),(86,88),(87,98),(90,91),(92,93),(96,97),(0,7),(35,48),(49,99)]
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
end Snaky.BreakerPostM31
