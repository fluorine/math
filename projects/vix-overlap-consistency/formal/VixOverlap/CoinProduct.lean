import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators

namespace VixOverlap.CoinProduct

abbrev Signs := Fin 6 → Bool

def Agree (seen : Finset (Fin 6)) (reference sample : Signs) : Prop :=
  ∀ i ∈ seen, reference i = sample i

def average (f : Signs → ℝ) : ℝ := (∑ sample, f sample) / 64

def maskedAverage (seen : Finset (Fin 6)) (reference : Signs) (f : Signs → ℝ) : ℝ := by
  classical
  exact average (fun sample => if Agree seen reference sample then f sample else 0)

def mass (seen : Finset (Fin 6)) : ℝ :=
  ∏ i : Fin 6, if i ∈ seen then (1 / 2 : ℝ) else 1

theorem average_product (f : Fin 6 → Bool → ℝ) :
    average (fun sample => ∏ i, f i (sample i)) =
      ∏ i, (f i false + f i true) / 2 := by
  unfold average
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, Finset.prod_div_distrib]
  norm_num [add_comm]

theorem maskedAverage_product (seen : Finset (Fin 6)) (reference : Signs)
    (f : Fin 6 → Bool → ℝ) :
    maskedAverage seen reference (fun sample => ∏ i, f i (sample i)) =
      ∏ i, if i ∈ seen then f i (reference i) / 2 else
        (f i false + f i true) / 2 := by
  classical
  have masked (sample : Signs) :
      (if Agree seen reference sample then ∏ i, f i (sample i) else 0) =
        ∏ i, if i ∈ seen → reference i = sample i then f i (sample i) else 0 := by
    rw [Fintype.prod_ite_zero]
    split_ifs <;> simp_all [Agree]
  unfold maskedAverage
  simp_rw [masked]
  rw [average_product (fun i b => if i ∈ seen → reference i = b then f i b else 0)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ seen
  · cases hr : reference i <;> simp [hi, hr]
  · simp [hi]

theorem maskedAverage_one (seen : Finset (Fin 6)) (reference : Signs) :
    maskedAverage seen reference (fun _ => 1) = mass seen := by
  have h := maskedAverage_product seen reference (fun _ _ => 1)
  simpa [mass] using h

theorem maskedAverage_const (seen : Finset (Fin 6)) (reference : Signs) (c : ℝ) :
    maskedAverage seen reference (fun _ => c) = c * mass seen := by
  classical
  rw [← maskedAverage_one seen reference]
  unfold maskedAverage average
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> simp_all

theorem maskedAverage_empty (reference : Signs) (f : Signs → ℝ) :
    maskedAverage ∅ reference f = average f := by
  simp [maskedAverage, Agree]

theorem mass_empty : mass ∅ = 1 := by simp [mass]

theorem average_one : average (fun _ => 1) = 1 := by
  rw [← maskedAverage_empty (fun _ => false), maskedAverage_one, mass_empty]

theorem maskedAverage_scale (seen : Finset (Fin 6)) (reference : Signs)
    (c : ℝ) (f : Signs → ℝ) :
    maskedAverage seen reference (fun sample => c * f sample) =
      c * maskedAverage seen reference f := by
  classical
  unfold maskedAverage average
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> simp_all

theorem average_const (c : ℝ) : average (fun _ => c) = c := by
  rw [← maskedAverage_empty (fun _ => false), maskedAverage_const, mass_empty, mul_one]

/-- Integration of an unobserved coordinate is its fair-coin mean times the
history mass. No division by that history mass occurs. -/
theorem maskedAverage_unseen_single (seen : Finset (Fin 6)) (reference : Signs)
    (coordinate : Fin 6) (unseen : coordinate ∉ seen) (f : Bool → ℝ) :
    maskedAverage seen reference (fun sample => f (sample coordinate)) =
      ((f false + f true) / 2) * mass seen := by
  classical
  have product (sample : Signs) :
      f (sample coordinate) =
        ∏ i : Fin 6, if i = coordinate then f (sample i) else 1 := by simp
  simp_rw [product]
  rw [maskedAverage_product (seen := seen) (reference := reference)
    (f := fun i b => if i = coordinate then f b else 1)]
  calc
    _ = (∏ i : Fin 6, if i = coordinate then (f false + f true) / 2 else 1) *
        mass seen := by
      unfold mass
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = coordinate
      · subst i
        simp [unseen]
      · by_cases hs : i ∈ seen <;> simp [hi, hs]
    _ = _ := by simp

/-- A product of independent mean-one factors is a martingale under coordinate
revelation, expressed entirely as unnormalized history equations. -/
theorem maskedAverage_martingale_product
    (seen later : Finset (Fin 6)) (included : seen ⊆ later) (reference : Signs)
    (factor : Fin 6 → Bool → ℝ)
    (mean_one : ∀ i, (factor i false + factor i true) / 2 = 1) :
    maskedAverage seen reference
        (fun sample => ∏ i : Fin 6, if i ∈ later then factor i (sample i) else 1) =
      (∏ i : Fin 6, if i ∈ seen then factor i (reference i) else 1) * mass seen := by
  classical
  rw [maskedAverage_product (seen := seen) (reference := reference)
    (f := fun i b => if i ∈ later then factor i b else 1)]
  unfold mass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i ∈ seen
  · simp [hs, included hs, div_eq_mul_inv]
  · by_cases hl : i ∈ later <;> simp [hs, hl, mean_one]

end VixOverlap.CoinProduct
