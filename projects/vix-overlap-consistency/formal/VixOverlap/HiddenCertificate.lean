import VixOverlap.HiddenData
import VixOverlap.ScheduleCertificate
import VixOverlap.Model

/-! Kernel-checked integer data and their exact real-probability interpretation.
The filtered-stock construction and ordinary-call bridge are separate modules. -/

open scoped BigOperators

namespace VixOverlap.Hidden

open ScheduleCertificate

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem numerator_pos : ∀ a : Atom, 0 < numerator a := by decide

theorem total_integer : (∑ a : Atom, numerator a) = 1024 := by decide

theorem prefix_integer : ∀ j k : Fin 7,
    (∑ a : Atom, if prefixCount (schedule a) j = k.val then numerator a else 0) =
      16 * prefixNumerator j k := by decide

theorem signal_integer : ∀ (w : Fin 3) (k : Fin 4),
    (∑ a : Atom, if signal a w = k.val then numerator a else 0) =
      16 * targetNumerator w k := by decide

theorem bit_integer : ∀ i : Fin 6,
    (∑ a : Atom, numerator a * bit (schedule a) i) = 512 := by decide

theorem history_integer : ∀ (a : Atom) (w : Fin 3),
    (∑ b : Atom, if History (w.val + 2) a b then
      (numerator b : ℤ) * ((windowCount (schedule b) w : ℤ) - signal a w) else 0) =
      0 := by decide

theorem weight_pos (a : Atom) : 0 < weight a :=
  div_pos (Nat.cast_pos.mpr (numerator_pos a)) (by norm_num)

theorem weight_nonneg (a : Atom) : 0 ≤ weight a := (weight_pos a).le

theorem weight_total : (∑ a : Atom, weight a) = 1 := by
  simp only [weight, ← Finset.sum_div, ← Nat.cast_sum]
  rw [total_integer]
  norm_num

noncomputable def law : FiniteLaw Atom where
  weight := weight
  nonneg := weight_nonneg
  total := weight_total

def latentFiltration : HistoryFiltration 7 Atom where
  partition := fun j => latentHistory j.val
  refines := by
    intro j k hjk a b h
    exact history_refines hjk h
  root := history_root

noncomputable def atomMass (f : Atom → ℕ) (k : ℕ) : ℝ :=
  ∑ a, if f a = k then weight a else 0

theorem nat_atom_mass (f : Atom → ℕ) (k : ℕ) :
    atomMass f k =
      ((∑ a, if f a = k then numerator a else 0 : ℕ) : ℝ) / 1024 := by
  simp only [atomMass, weight, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem prefix_mass (j k : Fin 7) :
    atomMass (fun a => prefixCount (schedule a) j) k.val = prefixTarget j k := by
  rw [nat_atom_mass, prefix_integer]
  simp only [Nat.cast_mul, Nat.cast_ofNat, prefixTarget]
  ring

theorem signal_mass (w : Fin 3) (k : Fin 4) :
    atomMass (fun a => signal a w) k.val = target w k := by
  rw [nat_atom_mass, signal_integer]
  simp only [Nat.cast_mul, Nat.cast_ofNat, target]
  ring

theorem integer_weighted_sum (f : Atom → ℤ) :
    (∑ a, weight a * (f a : ℝ)) =
      ((∑ a, (numerator a : ℤ) * f a : ℤ) : ℝ) / 1024 := by
  simp only [weight, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bit_mean (i : Fin 6) :
    (∑ a, weight a * (bit (schedule a) i : ℝ)) = 1 / 2 := by
  calc
    _ = ((∑ a, numerator a * bit (schedule a) i : ℕ) : ℝ) / 1024 := by
      simp only [weight, Nat.cast_sum, Nat.cast_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 1 / 2 := by rw [bit_integer]; norm_num

theorem history_window (a : Atom) (w : Fin 3) :
    (∑ b : Atom, if History (w.val + 2) a b then
      weight b * ((windowCount (schedule b) w : ℝ) - signal a w) else 0) = 0 := by
  have h := integer_weighted_sum (fun b => if History (w.val + 2) a b then
    (windowCount (schedule b) w : ℤ) - signal a w else 0)
  have hsum : (∑ b : Atom, (numerator b : ℤ) *
      (if History (w.val + 2) a b then
        (windowCount (schedule b) w : ℤ) - signal a w else 0)) = 0 := by
    simpa only [mul_ite, mul_zero] using history_integer a w
  rw [hsum] at h
  simpa only [Int.cast_ite, Int.cast_sub, Int.cast_natCast, Int.cast_zero,
    mul_ite, mul_zero, zero_div] using h

/-- Complete latent-data certificate. It does not assume a financial model. -/
theorem certificate :
    (∀ a : Atom, 0 < weight a) ∧ (∑ a : Atom, weight a) = 1 ∧
    (∀ j k : Fin 7,
      atomMass (fun a => prefixCount (schedule a) j) k.val = prefixTarget j k) ∧
    (∀ (w : Fin 3) (k : Fin 4), atomMass (fun a => signal a w) k.val = target w k) ∧
    (∀ i : Fin 6, (∑ a, weight a * (bit (schedule a) i : ℝ)) = 1 / 2) ∧
    (∀ (a : Atom) (w : Fin 3), (∑ b : Atom, if History (w.val + 2) a b then
      weight b * ((windowCount (schedule b) w : ℝ) - signal a w) else 0) = 0) :=
  ⟨weight_pos, weight_total, prefix_mass, signal_mass, bit_mean, history_window⟩

#print axioms certificate

end VixOverlap.Hidden
