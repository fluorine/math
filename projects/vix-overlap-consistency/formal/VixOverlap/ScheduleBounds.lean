import VixOverlap.ScheduleModel

noncomputable section
open scoped BigOperators

namespace VixOverlap.ScheduleModel

open ScheduleCertificate

theorem step_bounds (a : Schedule) (i : Fin 6) (up : Bool) :
    (1 / 2 : ℝ) ≤ step a i up ∧ step a i up ≤ 3 / 2 := by
  unfold step
  split_ifs <;> cases up <;> norm_num [coinStep]

theorem stockValue_bounds (a : Schedule) (signs : Signs) (event : ℕ) :
    (1 / 64 : ℝ) ≤ stockValue a signs event ∧ stockValue a signs event ≤ 729 / 64 := by
  rw [stockValue_eq_product]
  constructor
  · have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin 6)))
      (f := fun _ => (1 / 2 : ℝ))
      (g := fun i => if i ∈ observed event then step a i (signs i) else 1)
      (by intro; intro; norm_num)
      (by
        intro i _
        split_ifs
        · exact (step_bounds a i (signs i)).1
        · norm_num)
    norm_num at h ⊢
    exact h
  · have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin 6)))
      (f := fun i => if i ∈ observed event then step a i (signs i) else 1)
      (g := fun _ => (3 / 2 : ℝ))
      (by
        intro i _
        split_ifs
        · exact (step_pos _ _ _).le
        · exact zero_le_one)
      (by
        intro i _
        split_ifs
        · exact (step_bounds a i (signs i)).2
        · norm_num)
    norm_num at h ⊢
    exact h

theorem log_sixty_four : Real.log (64 : ℝ) = 6 * Real.log 2 := by
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
  norm_num

theorem stockValue_log_bound (a : Schedule) (signs : Signs) (event : ℕ) :
    |Real.log (stockValue a signs event)| ≤ 6 * Real.log 2 := by
  rcases stockValue_bounds a signs event with ⟨hlow, hupp⟩
  have low := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 64) hlow
  have upp := Real.log_le_log (stockValue_pos a signs event)
    (hupp.trans (by norm_num : (729 / 64 : ℝ) ≤ 64))
  have hinv : Real.log (1 / 64 : ℝ) = -6 * Real.log 2 := by
    rw [one_div, Real.log_inv, log_sixty_four]
    ring
  rw [hinv] at low
  rw [log_sixty_four] at upp
  exact abs_le.mpr ⟨by simpa only [neg_mul] using low, upp⟩

theorem cellBit_le_one (a : Schedule) (h : Fin 7) : cellBit a h ≤ 1 := by
  unfold cellBit
  split_ifs
  · exact zero_le_one
  · exact_mod_cast bit_le_one a _

theorem budgetValue_le_c (p : FiniteLaw Schedule) (j : Fin 8) (h : Fin 7)
    (state : State) : budgetValue p j h state ≤ c := by
  unfold budgetValue
  split_ifs
  · have hmean : (∑ a, p.weight a * cellBit a h) ≤ 1 := by
      calc
        _ ≤ ∑ a, p.weight a * 1 := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (cellBit_le_one a h) (p.nonneg a))
        _ = 1 := by simpa using p.total
    simpa using mul_le_mul_of_nonneg_left hmean c_nonneg
  · simpa using mul_le_mul_of_nonneg_left (cellBit_le_one state.1 h) c_nonneg

def futurePairs : Finset (Fin 8 × Fin 7) :=
  Finset.univ.filter (fun pair => pair.1.val ≤ pair.2.val)

theorem futurePairs_card : futurePairs.card = 28 := by decide

def gamma (p : FiniteLaw Schedule) (state : State) : ℝ :=
  1 + (∑ j : Fin 8, (|Real.log (stockValue state.1 state.2 j.val)| +
    stockValue state.1 state.2 j.val)) +
    ∑ pair ∈ futurePairs, budgetValue p pair.1 pair.2 state

def momentEnvelope : ℝ := 1 + 8 * (6 * Real.log 2 + 729 / 64) + 28 * c

def momentBound : ℝ := momentEnvelope ^ 2 + 1

theorem gamma_nonneg (p : FiniteLaw Schedule) (state : State) : 0 ≤ gamma p state := by
  unfold gamma
  exact add_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ =>
      add_nonneg (abs_nonneg _) (stockValue_pos _ _ _).le)))
    (Finset.sum_nonneg (fun pair _ => budgetValue_nonneg _ _ _ _))

theorem gamma_le (p : FiniteLaw Schedule) (state : State) : gamma p state ≤ momentEnvelope := by
  have hstock :
      (∑ j : Fin 8, (|Real.log (stockValue state.1 state.2 j.val)| +
        stockValue state.1 state.2 j.val)) ≤ 8 * (6 * Real.log 2 + 729 / 64) := by
    calc
      _ ≤ ∑ _ : Fin 8, (6 * Real.log 2 + 729 / 64) :=
        Finset.sum_le_sum (fun j _ => add_le_add (stockValue_log_bound _ _ _)
          (stockValue_bounds _ _ _).2)
      _ = _ := by simp <;> ring
  have hbudget : (∑ pair ∈ futurePairs, budgetValue p pair.1 pair.2 state) ≤ 28 * c := by
    calc
      _ ≤ ∑ _pair ∈ futurePairs, c :=
        Finset.sum_le_sum (fun pair _ => budgetValue_le_c _ _ _ _)
      _ = _ := by simp [futurePairs_card]
  exact add_le_add (add_le_add (le_refl 1) hstock) hbudget

theorem uniform_moment_bound (p : FiniteLaw Schedule) (state : State) :
    gamma p state ^ 2 < momentBound := by
  exact lt_of_le_of_lt (pow_le_pow_left₀ (gamma_nonneg p state) (gamma_le p state) 2)
    (lt_add_one _)

end VixOverlap.ScheduleModel
