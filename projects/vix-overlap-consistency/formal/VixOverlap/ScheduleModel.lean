import VixOverlap.Model
import VixOverlap.ScheduleStock
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192

namespace VixOverlap.ScheduleModel

open ScheduleCertificate

def grid : EventGrid 7 where
  time := fun j => j.val
  increasing := by
    intro j k hjk
    exact Nat.cast_lt.mpr hjk

def c : ℝ := -Real.log (3 / 4)

theorem c_eq_log_four_thirds : c = Real.log (4 / 3) := by
  have h := Real.log_inv (3 / 4 : ℝ)
  norm_num at h
  exact h.symm

theorem c_pos : 0 < c := by
  unfold c
  exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))

theorem c_nonneg : 0 ≤ c := c_pos.le

def history (event : ℕ) : Setoid State where
  r x y := event = 0 ∨
    x.1 = y.1 ∧ CoinProduct.Agree (observed event) x.2 y.2
  iseqv := {
    refl := by intro x; exact Or.inr ⟨rfl, fun _ _ => rfl⟩
    symm := by
      intro x y h
      rcases h with h | ⟨hxy, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨hxy.symm, fun i hi => (hs i hi).symm⟩
    trans := by
      intro x y z hxy hyz
      rcases hxy with h | ⟨ha, hs⟩
      · exact Or.inl h
      rcases hyz with h | ⟨hb, ht⟩
      · exact Or.inl h
      exact Or.inr ⟨ha.trans hb, fun i hi => (hs i hi).trans (ht i hi)⟩
  }

theorem history_rel (event : ℕ) (x y : State) :
    (history event).r x y ↔ event = 0 ∨
      x.1 = y.1 ∧ CoinProduct.Agree (observed event) x.2 y.2 := Iff.rfl

def filtration : HistoryFiltration 7 State where
  partition := fun j => history j.val
  refines := by
    intro j k hjk x y h
    by_cases hj : j.val = 0
    · exact Or.inl hj
    rcases h with hk | ⟨ha, hs⟩
    · exact (hj (by omega)).elim
    · exact Or.inr ⟨ha, fun i hi => hs i (observed_mono hjk hi)⟩
  root := by intro x y; exact Or.inl rfl

/-- Every schedule law uses exactly the same 4096 labeled states. A schedule
has weight `p(a)` and all 64 independent sign vectors are equiprobable. -/
def stateLaw (p : FiniteLaw Schedule) : FiniteLaw State where
  weight := fun state => p.weight state.1 / 64
  nonneg := by intro state; exact div_nonneg (p.nonneg _) (by norm_num)
  total := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ a, p.weight a := by
        apply Finset.sum_congr rfl
        intro a _
        simp [Fintype.card_fun, Signs, CoinProduct.Signs]
        ring
      _ = 1 := p.total

def cellBit (a : Schedule) (h : Fin 7) : ℝ :=
  if hh : h.val = 0 then 0 else
    (bit a ⟨h.val - 1, by have := h.isLt; omega⟩ : ℝ)

theorem cellBit_nonneg (a : Schedule) (h : Fin 7) : 0 ≤ cellBit a h := by
  unfold cellBit
  split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

theorem cellBit_zero (a : Schedule) : cellBit a 0 = 0 := by simp [cellBit]

theorem cellBit_succ (a : Schedule) (i : Fin 6) :
    cellBit a i.succ = (bit a i : ℝ) := by simp [cellBit]

def budgetValue (p : FiniteLaw Schedule) (j : Fin 8) (h : Fin 7) (state : State) : ℝ :=
  if j.val = 0 then c * ∑ a, p.weight a * cellBit a h else c * cellBit state.1 h

theorem budgetValue_nonneg (p : FiniteLaw Schedule) (j : Fin 8) (h : Fin 7)
    (state : State) : 0 ≤ budgetValue p j h state := by
  unfold budgetValue
  split_ifs
  · exact mul_nonneg c_nonneg (Finset.sum_nonneg (fun a _ =>
      mul_nonneg (p.nonneg a) (cellBit_nonneg a h)))
  · exact mul_nonneg c_nonneg (cellBit_nonneg _ _)

theorem budgetValue_cell_zero (p : FiniteLaw Schedule) (j : Fin 8) (state : State) :
    budgetValue p j 0 state = 0 := by simp [budgetValue, cellBit_zero]

theorem historySum_revealed (p : FiniteLaw Schedule) (event : ℕ) (hevent : event ≠ 0)
    (reference : State) (f : State → ℝ) :
    historySum (stateLaw p).weight (history event) reference f =
      p.weight reference.1 *
        CoinProduct.maskedAverage (observed event) reference.2
          (fun sample => f (reference.1, sample)) := by
  classical
  simp only [historySum, history_rel, stateLaw, hevent, false_or]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single reference.1]
  · simp only [true_and]
    unfold CoinProduct.maskedAverage CoinProduct.average
    rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro sample _
    split_ifs <;> simp_all <;> ring
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem historySum_root (p : FiniteLaw Schedule) (reference : State) (f : State → ℝ) :
    historySum (stateLaw p).weight (history 0) reference f =
      ∑ a, p.weight a * CoinProduct.average (fun sample => f (a, sample)) := by
  classical
  simp only [historySum, history_rel, stateLaw, true_or, ite_true]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  unfold CoinProduct.average
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sample _
  ring

theorem historyMass_root (p : FiniteLaw Schedule) (reference : State) :
    historyMass (stateLaw p).weight (history 0) reference = 1 := by
  unfold historyMass
  rw [historySum_root]
  simpa [CoinProduct.average_one] using p.total

theorem historyMass_revealed (p : FiniteLaw Schedule) (event : ℕ) (hevent : event ≠ 0)
    (reference : State) :
    historyMass (stateLaw p).weight (history event) reference =
      p.weight reference.1 * CoinProduct.mass (observed event) := by
  unfold historyMass
  rw [historySum_revealed p event hevent, CoinProduct.maskedAverage_one]

theorem historySum_schedule_function (p : FiniteLaw Schedule) (event : ℕ)
    (hevent : event ≠ 0) (reference : State) (f : Schedule → ℝ) :
    historySum (stateLaw p).weight (history event) reference (fun state => f state.1) =
      f reference.1 * historyMass (stateLaw p).weight (history event) reference := by
  rw [historySum_revealed p event hevent, historyMass_revealed p event hevent]
  change p.weight reference.1 *
      CoinProduct.maskedAverage (observed event) reference.2 (fun _ => f reference.1) = _
  rw [CoinProduct.maskedAverage_const]
  ring

theorem stock_martingale (p : FiniteLaw Schedule) (j k : ℕ) (hjk : j ≤ k)
    (reference : State) :
    historySum (stateLaw p).weight (history j) reference
        (fun state => stockValue state.1 state.2 k) =
      stockValue reference.1 reference.2 j *
        historyMass (stateLaw p).weight (history j) reference := by
  by_cases hj : j = 0
  · subst j
    rw [historySum_root, historyMass_root, stockValue_zero]
    simpa [stockValue_average] using p.total
  · rw [historySum_revealed p j hj, stockValue_masked_average _ _ _ hjk,
      historyMass_revealed p j hj]
    ring

theorem historySum_constant {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (information : Setoid Ω) (reference : Ω) (value : ℝ) :
    historySum p information reference (fun _ => value) =
      value * historyMass p information reference := by
  classical
  unfold historyMass
  unfold historySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> simp_all <;> ring

theorem step_log_average (a : Schedule) (i : Fin 6) :
    (-2 * Real.log (step a i false) + -2 * Real.log (step a i true)) / 2 =
      c * (bit a i : ℝ) := by
  rcases bit_zero_or_one a i with hb | hb
  · simp [step, hb]
  · have hlog := Real.log_mul
      (by norm_num : (1 / 2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)
    norm_num at hlog
    norm_num [step, hb, coinStep]
    unfold c
    rw [hlog]
    ring

theorem diagonal_step (p : FiniteLaw Schedule) (i : Fin 6) (reference : State) :
    historySum (stateLaw p).weight (history (i.val + 1)) reference
        (fun state => -2 * Real.log
          (stockValue state.1 state.2 (i.val + 2) /
            stockValue state.1 state.2 (i.val + 1))) =
      (c * (bit reference.1 i : ℝ)) *
        historyMass (stateLaw p).weight (history (i.val + 1)) reference := by
  simp_rw [stockValue_ratio]
  rw [historySum_revealed p (i.val + 1) (by omega),
    historyMass_revealed p (i.val + 1) (by omega)]
  rw [CoinProduct.maskedAverage_unseen_single (observed (i.val + 1)) reference.2
    i (by simp [observed]) (fun up => -2 * Real.log (step reference.1 i up))]
  rw [step_log_average]
  ring

theorem budget_tower (p : FiniteLaw Schedule) (j k : Fin 8) (h : Fin 7)
    (hjk : j ≤ k) (reference : State) :
    historySum (stateLaw p).weight (history j.val) reference (budgetValue p k h) =
      budgetValue p j h reference *
        historyMass (stateLaw p).weight (history j.val) reference := by
  by_cases hj : j.val = 0
  · by_cases hk : k.val = 0
    · have hkfun : budgetValue p k h =
          fun _ => c * ∑ a, p.weight a * cellBit a h := by
        funext state
        simp [budgetValue, hk]
      rw [hkfun, historySum_constant]
      simp [budgetValue, hj]
    · have hkfun : budgetValue p k h = fun state => c * cellBit state.1 h := by
        funext state
        simp [budgetValue, hk]
      rw [hkfun]
      simp only [budgetValue, hj, ite_true]
      rw [historySum_root, historyMass_root]
      change (∑ a, p.weight a * CoinProduct.average (fun _ => c * cellBit a h)) = _
      rw [show (∑ a, p.weight a * CoinProduct.average (fun _ => c * cellBit a h)) =
        ∑ a, p.weight a * (c * cellBit a h) by simp only [CoinProduct.average_const]]
      simp only [mul_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
  · have hk : k.val ≠ 0 := by omega
    have hkfun : budgetValue p k h = fun state => c * cellBit state.1 h := by
      funext state
      simp [budgetValue, hk]
    rw [hkfun]
    simp only [budgetValue, hj, ite_false]
    exact historySum_schedule_function p j.val hj reference (fun a => c * cellBit a h)

/-- The complete filtered financial model generated by an arbitrary schedule
law. All conditional rows are proved from the independent fair signs.
-/
def model (p : FiniteLaw Schedule) : FiniteModel grid State where
  law := stateLaw p
  filtration := filtration
  stock := fun j state => stockValue state.1 state.2 j.val
  budget := budgetValue p
  stock_pos := by intro j state; exact stockValue_pos _ _ _
  stock_initial := by intro state; exact stockValue_zero _ _
  stock_adapted := by
    intro j x y h
    rcases h with hj | ⟨ha, hs⟩
    · simp only [hj, stockValue_zero]
    · rw [ha]
      exact stockValue_adapted _ _ _ _ hs
  budget_nonneg := by
    intro j h state _
    exact budgetValue_nonneg _ _ _ _
  budget_adapted := by
    intro j h x y _ hxy
    rcases hxy with hj | ⟨ha, hs⟩
    · simp [budgetValue, hj]
    · simp [budgetValue, ha]
  martingale := by
    intro j k hjk reference
    exact stock_martingale p j.val k.val hjk reference
  diagonal := by
    intro h reference
    change historySum (stateLaw p).weight (history h.val) reference
      (fun state => -2 * Real.log
        (stockValue state.1 state.2 (h.val + 1) / stockValue state.1 state.2 h.val)) =
      budgetValue p h.castSucc h reference *
        historyMass (stateLaw p).weight (history h.val) reference
    refine Fin.cases ?_ (fun i => ?_) h
    · simp [stockValue_one, stockValue_zero, budgetValue_cell_zero, historySum]
    · simpa [filtration, budgetValue, cellBit_succ] using diagonal_step p i reference
  tower := by
    intro j k h hjk _ reference
    exact budget_tower p j k h hjk reference

def window (w : Fin 3) : Window 7 where
  start := ⟨w.val + 2, by omega⟩
  finish := ⟨w.val + 5, by omega⟩
  nonempty := by change w.val + 2 < w.val + 5; omega

theorem window_tenor (w : Fin 3) : (window w).tenor grid = 3 := by
  norm_num [Window.tenor, window, grid]

theorem model_windowBudget (p : FiniteLaw Schedule) (w : Fin 3) (state : State) :
    (model p).windowBudget (window w) state =
      c * (windowCount state.1 w : ℝ) := by
  simp only [FiniteModel.windowBudget, Window.cells, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases w <;>
    norm_num [window, model, budgetValue, cellBit, windowCount, Fin.sum_univ_succ] <;> ring

theorem model_vix (p : FiniteLaw Schedule) (w : Fin 3) (state : State) :
    (model p).vix (window w) state =
      Real.sqrt (c * (windowCount state.1 w : ℝ) / 3) := by
  unfold FiniteModel.vix FiniteModel.vixSquared
  rw [model_windowBudget, window_tenor]

theorem historySum_add {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (information : Setoid Ω) (reference : Ω) (f g : Ω → ℝ) :
    historySum p information reference (fun state => f state + g state) =
      historySum p information reference f + historySum p information reference g := by
  classical
  unfold historySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> simp_all <;> ring

theorem conditional_log_step (p : FiniteLaw Schedule) (j : ℕ) (hj : j ≠ 0)
    (i : Fin 6) (future : j ≤ i.val + 1) (reference : State) :
    historySum (stateLaw p).weight (history j) reference
        (fun state => -2 * Real.log (step state.1 i (state.2 i))) =
      (c * (bit reference.1 i : ℝ)) *
        historyMass (stateLaw p).weight (history j) reference := by
  rw [historySum_revealed p j hj, historyMass_revealed p j hj]
  rw [CoinProduct.maskedAverage_unseen_single (observed j) reference.2
    i (by simp [observed]; omega) (fun up => -2 * Real.log (step reference.1 i up))]
  rw [step_log_average]
  ring

def windowIndex (w : Fin 3) (r : Fin 3) : Fin 6 :=
  ⟨w.val + r.val + 1, by omega⟩

theorem stockValue_window_ratio (a : Schedule) (signs : Signs) (w : Fin 3) :
    stockValue a signs (w.val + 5) / stockValue a signs (w.val + 2) =
      step a (windowIndex w 0) (signs (windowIndex w 0)) *
      step a (windowIndex w 1) (signs (windowIndex w 1)) *
      step a (windowIndex w 2) (signs (windowIndex w 2)) := by
  have h0 := stockValue_succ a signs (windowIndex w 0)
  have h1 := stockValue_succ a signs (windowIndex w 1)
  have h2 := stockValue_succ a signs (windowIndex w 2)
  norm_num [windowIndex, Nat.add_assoc] at h0 h1 h2
  rw [div_eq_iff (stockValue_pos _ _ _).ne']
  rw [h2, h1, h0]
  norm_num [windowIndex]
  ring

theorem window_log_return (a : Schedule) (signs : Signs) (w : Fin 3) :
    -2 * Real.log (stockValue a signs (w.val + 5) / stockValue a signs (w.val + 2)) =
      (-2 * Real.log (step a (windowIndex w 0) (signs (windowIndex w 0))) +
        -2 * Real.log (step a (windowIndex w 1) (signs (windowIndex w 1)))) +
        -2 * Real.log (step a (windowIndex w 2) (signs (windowIndex w 2))) := by
  rw [stockValue_window_ratio,
    Real.log_mul (mul_ne_zero (step_pos _ _ _).ne' (step_pos _ _ _).ne')
      (step_pos _ _ _).ne',
    Real.log_mul (step_pos _ _ _).ne' (step_pos _ _ _).ne']
  ring

/-- The full conditional log-contract identity for the whole VIX window,
without conditioning on a positive-mass history or dividing by its mass. -/
theorem model_window_log_identity (p : FiniteLaw Schedule) (w : Fin 3)
    (reference : State) :
    historySum (model p).law.weight ((model p).filtration.partition (window w).start)
        reference (fun state => -2 * Real.log
          ((model p).stock (window w).finish state /
            (model p).stock (window w).start state)) =
      (model p).windowBudget (window w) reference *
        historyMass (model p).law.weight
          ((model p).filtration.partition (window w).start) reference := by
  change historySum (stateLaw p).weight (history (w.val + 2)) reference
      (fun state => -2 * Real.log
        (stockValue state.1 state.2 (w.val + 5) /
          stockValue state.1 state.2 (w.val + 2))) = _
  simp_rw [window_log_return]
  rw [historySum_add, historySum_add]
  rw [conditional_log_step p (w.val + 2) (by omega) (windowIndex w 0)
    (by simp [windowIndex]),
    conditional_log_step p (w.val + 2) (by omega) (windowIndex w 1)
    (by simp [windowIndex]),
    conditional_log_step p (w.val + 2) (by omega) (windowIndex w 2)
    (by simp [windowIndex])]
  rw [model_windowBudget]
  norm_num [model, filtration, window, windowCount, Fin.sum_univ_succ, windowIndex]
  ring

theorem model_root_budget (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2)
    (i : Fin 6) (state : State) :
    (model p).budget 0 i.succ state = c / 2 := by
  simp only [model, budgetValue, Fin.val_zero, ite_true, cellBit_succ, mean]
  ring

def uniformScheduleLaw : FiniteLaw Schedule where
  weight := fun _ => 1 / 64
  nonneg := by intro; norm_num
  total := by norm_num [Schedule]

theorem uniform_bit_sum : ∀ i : Fin 6, (∑ a : Schedule, bit a i) = 32 := by decide

theorem uniform_bit_mean (i : Fin 6) :
    (∑ a, uniformScheduleLaw.weight a * (bit a i : ℝ)) = 1 / 2 := by
  change (∑ a : Schedule, (1 / 64 : ℝ) * (bit a i : ℝ)) = _
  rw [← Finset.mul_sum, ← Nat.cast_sum, uniform_bit_sum]
  norm_num

/-- A nondegenerate admissible example in the declared schedule architecture:
every active future cell has strictly positive common root budget. -/
theorem uniform_model_nonzero (i : Fin 6) (state : State) :
    0 < (model uniformScheduleLaw).budget 0 i.succ state := by
  rw [model_root_budget uniformScheduleLaw uniform_bit_mean]
  exact div_pos c_pos (by norm_num)

end VixOverlap.ScheduleModel
