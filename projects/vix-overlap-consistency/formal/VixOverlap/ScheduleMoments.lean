import VixOverlap.ScheduleModel

noncomputable section
open scoped BigOperators

namespace VixOverlap

namespace CoinProduct

theorem average_finset_sum {ι : Type*} (indices : Finset ι) (f : ι → Signs → ℝ) :
    average (fun sample => ∑ i ∈ indices, f i sample) =
      ∑ i ∈ indices, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

end CoinProduct

namespace ScheduleModel

open ScheduleCertificate

theorem model_expectation_eq_root (p : FiniteLaw Schedule) (reference : State)
    (f : State → ℝ) :
    (model p).expectation f = historySum (stateLaw p).weight (history 0) reference f := by
  simp only [FiniteModel.expectation, model, historySum, history_rel, true_or, ite_true]

theorem model_expectation_eq_schedule_average (p : FiniteLaw Schedule) (f : State → ℝ) :
    (model p).expectation f =
      ∑ a, p.weight a * CoinProduct.average (fun signs => f (a, signs)) := by
  rw [model_expectation_eq_root p (0, fun _ => false), historySum_root]

theorem model_stock_forward (p : FiniteLaw Schedule) (j : Fin 8) :
    (model p).expectation ((model p).stock j) = 1 := by
  rw [model_expectation_eq_schedule_average]
  change (∑ a, p.weight a * CoinProduct.average
    (fun signs => stockValue a signs j.val)) = 1
  simpa [stockValue_average] using p.total

theorem average_log_step (a : Schedule) (i : Fin 6) :
    CoinProduct.average (fun signs => -2 * Real.log (step a i (signs i))) =
      c * (bit a i : ℝ) := by
  have h := CoinProduct.maskedAverage_unseen_single ∅ (fun _ => false) i
    (by simp) (fun up => -2 * Real.log (step a i up))
  rw [CoinProduct.maskedAverage_empty, CoinProduct.mass_empty, mul_one, step_log_average] at h
  exact h

theorem log_stock_value (a : Schedule) (signs : Signs) (event : ℕ) :
    -2 * Real.log (stockValue a signs event) =
      ∑ i : Fin 6, if i ∈ observed event then
        -2 * Real.log (step a i (signs i)) else 0 := by
  rw [stockValue_eq_product]
  rw [Real.log_prod (by
    intro i _
    split_ifs
    · exact (step_pos _ _ _).ne'
    · exact one_ne_zero)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem average_log_stock (a : Schedule) (k : Fin 7) :
    CoinProduct.average (fun signs => -2 * Real.log (stockValue a signs (k.val + 1))) =
      c * (prefixCount a k : ℝ) := by
  simp_rw [log_stock_value]
  rw [CoinProduct.average_finset_sum]
  calc
    _ = ∑ i : Fin 6, if i.val < k.val then c * (bit a i : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k.val
      · have hi' : i ∈ observed (k.val + 1) := by simp [observed]; omega
        simp only [hi', ite_true, average_log_step, hi]
      · have hi' : i ∉ observed (k.val + 1) := by simp [observed]; omega
        simp only [hi', ite_false, CoinProduct.average_const, hi]
    _ = c * (prefixCount a k : ℝ) := by
      simp [prefixCount, Nat.cast_sum, Finset.mul_sum]

theorem model_expected_log_stock (p : FiniteLaw Schedule) (k : Fin 7) :
    (model p).expectation (fun state =>
      -2 * Real.log (stockValue state.1 state.2 (k.val + 1))) =
      c * ∑ a, p.weight a * (prefixCount a k : ℝ) := by
  rw [model_expectation_eq_schedule_average]
  change (∑ a, p.weight a * CoinProduct.average (fun signs =>
    -2 * Real.log (stockValue a signs (k.val + 1)))) = _
  simp_rw [average_log_stock]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem prefix_mean_of_bit_mean (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2)
    (k : Fin 7) :
    (∑ a, p.weight a * (prefixCount a k : ℝ)) = (k.val : ℝ) / 2 := by
  have hcast (a : Schedule) : (prefixCount a k : ℝ) =
      ∑ i : Fin 6, if i.val < k.val then (bit a i : ℝ) else 0 := by
    simp [prefixCount, Nat.cast_sum]
  simp_rw [hcast, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hslots := congrArg (fun n : ℕ => (n : ℝ)) (prefix_slots k)
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hslots
  calc
    _ = ∑ i : Fin 6, if i.val < k.val then (1 / 2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k.val <;> simp [hi, mean]
    _ = (∑ i : Fin 6, if i.val < k.val then (1 : ℝ) else 0) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = (k.val : ℝ) / 2 := by rw [hslots]

theorem model_expected_log_ratio (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2)
    (j k : Fin 7) :
    (model p).expectation (fun state => -2 * Real.log
      (stockValue state.1 state.2 (k.val + 1) /
        stockValue state.1 state.2 (j.val + 1))) =
      c * ((k.val : ℝ) - (j.val : ℝ)) / 2 := by
  have pointwise (state : State) :
      -2 * Real.log (stockValue state.1 state.2 (k.val + 1) /
          stockValue state.1 state.2 (j.val + 1)) =
        (-2 * Real.log (stockValue state.1 state.2 (k.val + 1))) -
          (-2 * Real.log (stockValue state.1 state.2 (j.val + 1))) := by
    rw [Real.log_div (stockValue_pos _ _ _).ne' (stockValue_pos _ _ _).ne']
    ring
  simp_rw [pointwise]
  have linear : (model p).expectation (fun state =>
      (-2 * Real.log (stockValue state.1 state.2 (k.val + 1))) -
        (-2 * Real.log (stockValue state.1 state.2 (j.val + 1)))) =
      (model p).expectation (fun state => -2 * Real.log (stockValue state.1 state.2 (k.val + 1))) -
        (model p).expectation (fun state => -2 * Real.log (stockValue state.1 state.2 (j.val + 1))) := by
    simp only [FiniteModel.expectation, mul_sub, Finset.sum_sub_distrib]
  rw [linear, model_expected_log_stock, model_expected_log_stock,
    prefix_mean_of_bit_mean p mean, prefix_mean_of_bit_mean p mean]
  ring

theorem model_expected_window_log (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2) (w : Fin 3) :
    (model p).expectation (fun state => -2 * Real.log
      ((model p).stock (window w).finish state /
        (model p).stock (window w).start state)) = 3 * c / 2 := by
  have h := model_expected_log_ratio p mean
    (⟨w.val + 1, by omega⟩ : Fin 7) (⟨w.val + 4, by omega⟩ : Fin 7)
  convert h using 1 <;> norm_num [model, window, Nat.add_assoc] <;> ring

theorem window_count_mean_of_bit_mean (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2) (w : Fin 3) :
    (∑ a, p.weight a * (windowCount a w : ℝ)) = 3 / 2 := by
  unfold windowCount
  simp_rw [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mean]
  norm_num

theorem model_vix_second_moment (p : FiniteLaw Schedule)
    (mean : ∀ i : Fin 6, (∑ a, p.weight a * (bit a i : ℝ)) = 1 / 2) (w : Fin 3) :
    (model p).expectation (fun state => (model p).vix (window w) state ^ 2) = c / 2 := by
  have square (state : State) : (model p).vix (window w) state ^ 2 =
      c * (windowCount state.1 w : ℝ) / 3 := by
    rw [model_vix]
    exact Real.sq_sqrt (div_nonneg (mul_nonneg c_nonneg (Nat.cast_nonneg _)) (by norm_num))
  simp_rw [square]
  rw [model_expectation_eq_schedule_average]
  change (∑ a, p.weight a * CoinProduct.average
    (fun _ => c * (windowCount a w : ℝ) / 3)) = _
  simp only [CoinProduct.average_const]
  calc
    _ = (c / 3) * (∑ a, p.weight a * (windowCount a w : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = c / 2 := by rw [window_count_mean_of_bit_mean p mean]; ring

theorem model_overlap_log_cost (p : FiniteLaw Schedule)
    (mean : ∀ h : Fin 6, (∑ a, p.weight a * (bit a h : ℝ)) = 1 / 2)
    (i j : Fin 3) :
    -(2 / 3 : ℝ) * (model p).expectation (fun state =>
      Real.log ((model p).stock (window j).start state) -
        Real.log ((model p).stock (window i).start state)) =
      c * ((j.val : ℝ) - (i.val : ℝ)) / 6 := by
  have h := model_expected_log_ratio p mean
    (⟨i.val + 1, by omega⟩ : Fin 7) (⟨j.val + 1, by omega⟩ : Fin 7)
  have pointwise (state : State) :
      -2 * Real.log (stockValue state.1 state.2 (j.val + 2) /
          stockValue state.1 state.2 (i.val + 2)) =
        -2 * (Real.log (stockValue state.1 state.2 (j.val + 2)) -
          Real.log (stockValue state.1 state.2 (i.val + 2))) := by
    rw [Real.log_div (stockValue_pos _ _ _).ne' (stockValue_pos _ _ _).ne']
  have scalar (f : State → ℝ) :
      (model p).expectation (fun state => -2 * f state) =
        -2 * (model p).expectation f := by
    simp only [FiniteModel.expectation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    ring
  simp only [Fin.val_mk, Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at h
  simp_rw [pointwise] at h
  rw [scalar] at h
  change -(2 / 3 : ℝ) * (model p).expectation (fun state =>
    Real.log (stockValue state.1 state.2 (j.val + 2)) -
      Real.log (stockValue state.1 state.2 (i.val + 2))) = _
  calc
    _ = (1 / 3 : ℝ) * (-2 * (model p).expectation (fun state =>
      Real.log (stockValue state.1 state.2 (j.val + 2)) -
        Real.log (stockValue state.1 state.2 (i.val + 2)))) := by ring
    _ = (1 / 3 : ℝ) * (c * (((j.val : ℝ) + 1) - ((i.val : ℝ) + 1)) / 2) := by rw [h]
    _ = _ := by ring

end ScheduleModel
end VixOverlap
