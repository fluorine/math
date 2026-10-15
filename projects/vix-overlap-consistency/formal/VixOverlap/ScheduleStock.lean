import VixOverlap.ScheduleData
import VixOverlap.CoinProduct
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators

namespace VixOverlap.ScheduleModel

open ScheduleCertificate
abbrev Signs := CoinProduct.Signs
abbrev State := Schedule × Signs

/-- Information about signs of cells whose ends have occurred. Cell zero in
the schedule is the event-1 to event-2 cell. -/
def observed (event : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => i.val + 1 < event)

def activeSet (a : Schedule) (event : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => i.val + 1 < event ∧ bit a i = 1)

def coinStep (up : Bool) : ℝ := if up then 3 / 2 else 1 / 2

def step (a : Schedule) (i : Fin 6) (up : Bool) : ℝ :=
  if bit a i = 1 then coinStep up else 1

def stockValue (a : Schedule) (signs : Signs) (event : ℕ) : ℝ :=
  ∏ i ∈ activeSet a event, coinStep (signs i)

def upCount (a : Schedule) (signs : Signs) (k : Fin 7) : ℕ :=
  ((activeSet a (k.val + 1)).filter (fun i => signs i = true)).card

theorem bit_zero_or_one (a : Schedule) (i : Fin 6) : bit a i = 0 ∨ bit a i = 1 := by
  have := bit_le_one a i
  omega

theorem coinStep_pos (up : Bool) : 0 < coinStep up := by
  cases up <;> norm_num [coinStep]

theorem step_pos (a : Schedule) (i : Fin 6) (up : Bool) : 0 < step a i up := by
  unfold step
  split_ifs
  · exact coinStep_pos _
  · exact zero_lt_one

theorem step_average (a : Schedule) (i : Fin 6) :
    (step a i false + step a i true) / 2 = 1 := by
  unfold step
  split_ifs <;> norm_num [coinStep]

theorem stockValue_pos (a : Schedule) (signs : Signs) (event : ℕ) :
    0 < stockValue a signs event :=
  Finset.prod_pos (fun _ _ => coinStep_pos _)

theorem observed_zero : observed 0 = ∅ := by simp [observed]
theorem observed_one : observed 1 = ∅ := by simp [observed]

theorem activeSet_zero (a : Schedule) : activeSet a 0 = ∅ := by simp [activeSet]
theorem activeSet_one (a : Schedule) : activeSet a 1 = ∅ := by simp [activeSet]

theorem stockValue_zero (a : Schedule) (signs : Signs) : stockValue a signs 0 = 1 := by
  simp [stockValue, activeSet_zero]

theorem stockValue_one (a : Schedule) (signs : Signs) : stockValue a signs 1 = 1 := by
  simp [stockValue, activeSet_one]

theorem observed_mono {j k : ℕ} (hjk : j ≤ k) : observed j ⊆ observed k := by
  intro i hi
  simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem activeSet_subset_observed (a : Schedule) (event : ℕ) :
    activeSet a event ⊆ observed event := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩

theorem stockValue_adapted (a : Schedule) (event : ℕ) (s t : Signs)
    (h : CoinProduct.Agree (observed event) s t) :
    stockValue a s event = stockValue a t event := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i (activeSet_subset_observed a event hi)]

theorem stockValue_eq_product (a : Schedule) (signs : Signs) (event : ℕ) :
    stockValue a signs event =
      ∏ i : Fin 6, if i ∈ observed event then step a i (signs i) else 1 := by
  unfold stockValue activeSet
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i.val + 1 < event <;> by_cases ha : bit a i = 1 <;>
    simp [observed, step, hi, ha]

theorem stockValue_masked_average (a : Schedule) (j k : ℕ) (hjk : j ≤ k)
    (reference : Signs) :
    CoinProduct.maskedAverage (observed j) reference
        (fun signs => stockValue a signs k) =
      stockValue a reference j * CoinProduct.mass (observed j) := by
  simp_rw [stockValue_eq_product]
  exact CoinProduct.maskedAverage_martingale_product (observed j) (observed k)
    (observed_mono hjk) reference (step a) (step_average a)

theorem stockValue_average (a : Schedule) (event : ℕ) :
    CoinProduct.average (fun signs => stockValue a signs event) = 1 := by
  have h := stockValue_masked_average a 0 event (Nat.zero_le _) (fun _ => false)
  simpa [observed_zero, CoinProduct.maskedAverage_empty, stockValue_zero,
    CoinProduct.mass_empty] using h

theorem stockValue_succ (a : Schedule) (signs : Signs) (i : Fin 6) :
    stockValue a signs (i.val + 2) =
      stockValue a signs (i.val + 1) * step a i (signs i) := by
  have local_factor (h : Fin 6) :
      (if h ∈ observed (i.val + 2) then step a h (signs h) else 1) =
        (if h ∈ observed (i.val + 1) then step a h (signs h) else 1) *
          (if h = i then step a i (signs i) else 1) := by
    by_cases hi : h = i
    · subst h
      simp [observed]
    · have hne : h.val ≠ i.val := fun he => hi (Fin.ext he)
      simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and,
        hi, ite_false, mul_one]
      simp only [show h.val + 1 < i.val + 2 ↔ h.val + 1 < i.val + 1 by omega]
  simp_rw [stockValue_eq_product, local_factor]
  rw [Finset.prod_mul_distrib]
  simp

theorem stockValue_ratio (a : Schedule) (signs : Signs) (i : Fin 6) :
    stockValue a signs (i.val + 2) / stockValue a signs (i.val + 1) =
      step a i (signs i) := by
  rw [stockValue_succ, mul_comm, mul_div_cancel_right₀]
  exact (stockValue_pos _ _ _).ne'

theorem activeSet_card (a : Schedule) (k : Fin 7) :
    (activeSet a (k.val + 1)).card = prefixCount a k := by
  simp only [activeSet, Finset.card_eq_sum_ones, Finset.sum_filter, prefixCount]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val + 1 < k.val + 1 ↔ i.val < k.val := by omega
  rcases bit_zero_or_one a i with hb | hb <;> simp [hi, hb]

theorem upCount_le (a : Schedule) (signs : Signs) (k : Fin 7) :
    upCount a signs k ≤ prefixCount a k := by
  rw [← activeSet_card]
  exact Finset.card_filter_le _ _

theorem stockValue_formula (a : Schedule) (signs : Signs) (k : Fin 7) :
    stockValue a signs (k.val + 1) =
      (3 : ℝ) ^ upCount a signs k / 2 ^ prefixCount a k := by
  have factor (i : Fin 6) :
      coinStep (signs i) = (if signs i = true then (3 : ℝ) else 1) / 2 := by
    cases signs i <;> norm_num [coinStep]
  unfold stockValue
  simp_rw [factor]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, activeSet_card]
  congr 1
  simp [Finset.prod_ite, upCount]

/-- A coordinate permutation matches the entire conditional stock law whenever
the same number of active cells has elapsed. This holds for every payoff.
-/
theorem uniform_stock_function_eq_of_activeSet_card_eq
    (a b : Schedule) (event : ℕ)
    (h : (activeSet a event).card = (activeSet b event).card) (payoff : ℝ → ℝ) :
    CoinProduct.average (fun signs => payoff (stockValue a signs event)) =
      CoinProduct.average (fun signs => payoff (stockValue b signs event)) := by
  classical
  obtain ⟨permutation, hp⟩ := Equiv.Perm.exists_map_finset_eq
    (activeSet a event) (activeSet b event) h
  let transport : Signs ≃ Signs := permutation.arrowCongr (Equiv.refl Bool)
  have path (signs : Signs) :
      stockValue a signs event = stockValue b (transport signs) event := by
    unfold stockValue
    rw [← hp, Finset.prod_map]
    simp [transport, Equiv.arrowCongr]
  unfold CoinProduct.average
  congr 1
  exact Fintype.sum_equiv transport _ _ (fun signs => congrArg payoff (path signs))

theorem uniform_stock_function_eq_of_prefixCount_eq
    (a b : Schedule) (k : Fin 7) (h : prefixCount a k = prefixCount b k)
    (payoff : ℝ → ℝ) :
    CoinProduct.average (fun signs => payoff (stockValue a signs (k.val + 1))) =
      CoinProduct.average (fun signs => payoff (stockValue b signs (k.val + 1))) :=
  uniform_stock_function_eq_of_activeSet_card_eq a b (k.val + 1)
    (by simpa [activeSet_card] using h) payoff

end VixOverlap.ScheduleModel
