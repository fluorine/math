import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace VixOverlap.ScheduleCertificate

abbrev Schedule := Fin 64

/-- Bits are numbered from left to right in the binary expansion. -/
def bit (a : Schedule) (h : Fin 6) : ℕ :=
  a.val / 2 ^ (5 - h.val) % 2

theorem bit_lt_two (a : Schedule) (h : Fin 6) : bit a h < 2 :=
  Nat.mod_lt _ (by decide)

theorem bit_le_one (a : Schedule) (h : Fin 6) : bit a h ≤ 1 := by
  have := bit_lt_two a h
  omega

/-- The number of active cells among the first `j` cells. -/
def prefixCount (a : Schedule) (j : Fin 7) : ℕ :=
  ∑ h : Fin 6, if h.val < j.val then bit a h else 0

/-- Window `w` contains cells `w+1`, `w+2`, `w+3`, with zero-based indices. -/
def windowCount (a : Schedule) (w : Fin 3) : ℕ :=
  ∑ r : Fin 3, bit a ⟨w.val + r.val + 1, by omega⟩

theorem prefix_slots : ∀ j : Fin 7,
    (∑ h : Fin 6, if h.val < j.val then 1 else 0) = j.val := by decide

theorem prefixCount_le_time (a : Schedule) (j : Fin 7) : prefixCount a j ≤ j.val := by
  rw [← prefix_slots j]
  apply Finset.sum_le_sum
  intro h _
  split_ifs
  · exact bit_le_one a h
  · exact le_rfl

theorem prefixCount_le_six (a : Schedule) (j : Fin 7) : prefixCount a j ≤ 6 := by
  have hc := prefixCount_le_time a j
  omega

theorem windowCount_le_three (a : Schedule) (w : Fin 3) : windowCount a w ≤ 3 := by
  calc
    windowCount a w ≤ ∑ _ : Fin 3, (1 : ℕ) :=
      Finset.sum_le_sum (fun _ _ => bit_le_one _ _)
    _ = 3 := by simp

end VixOverlap.ScheduleCertificate
