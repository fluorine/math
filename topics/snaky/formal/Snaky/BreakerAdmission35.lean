import Snaky.BreakerAdmission35Group0
import Snaky.BreakerAdmission35Group1
import Snaky.BreakerAdmission35Group2
import Snaky.BreakerAdmission35Group3
import Snaky.BreakerAdmission35Group4
import Snaky.BreakerAdmission35Group5
import Snaky.BreakerAdmission35Group6
import Snaky.Geometry10

namespace Snaky.BreakerAdmission35
open Snaky.Breaker

private theorem group0_defense (u : Nat) (hu : u ∈ G0.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G0.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G0.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G0.literal_coverage u hu

private theorem group1_defense (u : Nat) (hu : u ∈ G1.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G1.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G1.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G1.literal_coverage u hu

private theorem group2_defense (u : Nat) (hu : u ∈ G2.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G2.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G2.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G2.literal_coverage u hu

private theorem group3_defense (u : Nat) (hu : u ∈ G3.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G3.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G3.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G3.literal_coverage u hu

private theorem group4_defense (u : Nat) (hu : u ∈ G4.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G4.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G4.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G4.literal_coverage u hu

private theorem group5_defense (u : Nat) (hu : u ∈ G5.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G5.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G5.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G5.literal_coverage u hu

private theorem group6_defense (u : Nat) (hu : u ∈ G6.groupEntries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have he : u ∈ entries := by
    have h : ∀ x ∈ G6.groupEntries, x ∈ entries := by decide +kernel
    exact h u hu
  apply pristine_switch_not_blackWins (colors_disjoint u he) (reserved_fresh u he)
    (G6.matching u hu) P52.guard_shape P52.switch_rows
  rw [Geometry10.placements_eq_targets]
  exact G6.literal_coverage u hu

/-- Thirty-five complete conditional successor defenses, not a complete A52 root. -/
theorem not_blackWins (u : Nat) (hu : u ∈ entries) :
    ¬ BlackWins (placements 10 10 snaky) 100 (maker u) breaker := by
  have cases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9 ∨ u = 19 ∨ u = 29 ∨ u = 32 ∨ u = 35 ∨ u = 39 ∨ u = 48 ∨ u = 49 ∨ u = 59 ∨ u = 60 ∨ u = 62 ∨ u = 69 ∨ u = 72 ∨ u = 79 ∨ u = 80 ∨ u = 81 ∨ u = 87 ∨ u = 88 ∨ u = 89 ∨ u = 90 ∨ u = 91 ∨ u = 92 ∨ u = 93 ∨ u = 95 ∨ u = 96 ∨ u = 97 ∨ u = 98 ∨ u = 99 := by
    simpa only [entries,List.mem_cons,List.not_mem_nil,or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact group0_defense 0 (by decide)
  · exact group0_defense 1 (by decide)
  · exact group0_defense 2 (by decide)
  · exact group0_defense 5 (by decide)
  · exact group0_defense 6 (by decide)
  · exact group1_defense 7 (by decide)
  · exact group1_defense 8 (by decide)
  · exact group1_defense 9 (by decide)
  · exact group1_defense 19 (by decide)
  · exact group1_defense 29 (by decide)
  · exact group2_defense 32 (by decide)
  · exact group2_defense 35 (by decide)
  · exact group2_defense 39 (by decide)
  · exact group2_defense 48 (by decide)
  · exact group2_defense 49 (by decide)
  · exact group3_defense 59 (by decide)
  · exact group3_defense 60 (by decide)
  · exact group3_defense 62 (by decide)
  · exact group3_defense 69 (by decide)
  · exact group3_defense 72 (by decide)
  · exact group4_defense 79 (by decide)
  · exact group4_defense 80 (by decide)
  · exact group4_defense 81 (by decide)
  · exact group4_defense 87 (by decide)
  · exact group4_defense 88 (by decide)
  · exact group5_defense 89 (by decide)
  · exact group5_defense 90 (by decide)
  · exact group5_defense 91 (by decide)
  · exact group5_defense 92 (by decide)
  · exact group5_defense 93 (by decide)
  · exact group6_defense 95 (by decide)
  · exact group6_defense 96 (by decide)
  · exact group6_defense 97 (by decide)
  · exact group6_defense 98 (by decide)
  · exact group6_defense 99 (by decide)

end Snaky.BreakerAdmission35
