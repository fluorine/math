import VixOverlap.HiddenCertificate
import VixOverlap.FiniteConditioning
import VixOverlap.BroadContract

noncomputable section
open scoped BigOperators

namespace VixOverlap.HiddenModel

open ScheduleCertificate ScheduleModel FiniteConditioning

abbrev Raw := Hidden.Atom × Signs

def rawLaw : FiniteLaw Raw where
  weight := fun s => Hidden.weight s.1 / 64
  nonneg := by intro s; exact div_nonneg (Hidden.weight_pos s.1).le (by norm_num)
  total := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ a, Hidden.weight a := by
        apply Finset.sum_congr rfl
        intro a _
        simp [Signs, CoinProduct.Signs]
        ring
      _ = 1 := Hidden.weight_total

def rawHistory (j : ℕ) : Setoid Raw where
  r s t := Hidden.History j s.1 t.1 ∧ CoinProduct.Agree (observed j) s.2 t.2
  iseqv := {
    refl := fun s => ⟨Hidden.history_refl j s.1, fun _ _ => rfl⟩
    symm := fun h => ⟨Hidden.history_symm h.1, fun i hi => (h.2 i hi).symm⟩
    trans := fun h k => ⟨Hidden.history_trans h.1 k.1,
      fun i hi => (h.2 i hi).trans (k.2 i hi)⟩ }

theorem raw_history_rel (j : ℕ) (s t : Raw) :
    (rawHistory j).r s t ↔
      Hidden.History j s.1 t.1 ∧ CoinProduct.Agree (observed j) s.2 t.2 := Iff.rfl

theorem latent_history_rel (j : ℕ) (a b : Hidden.Atom) :
    (Hidden.latentHistory j).r a b ↔ Hidden.History j a b := Iff.rfl

def filtration : HistoryFiltration 7 Raw where
  partition := fun j => rawHistory j.val
  refines := by
    intro j k hjk s t h
    exact ⟨Hidden.history_refines hjk h.1,
      fun i hi => h.2 i (observed_mono hjk hi)⟩
  root := by
    intro s t
    refine ⟨Hidden.history_root _ _, ?_⟩
    simp [CoinProduct.Agree, observed_zero]

def conditionalBudget (j : ℕ) (h : Fin 7) (a : Hidden.Atom) : ℝ :=
  c * conditionalAverage Hidden.law (Hidden.latentHistory j)
    (fun b => cellBit (Hidden.schedule b) h) a

theorem latent_mass_pos (j : ℕ) (a : Hidden.Atom) :
    0 < historyMass Hidden.law.weight (Hidden.latentHistory j) a :=
  mass_pos_of_weight_pos Hidden.law _ a (Hidden.weight_pos a)

theorem raw_history_sum (j : ℕ) (reference : Raw) (f : Raw → ℝ) :
    historySum rawLaw.weight (rawHistory j) reference f =
      historySum Hidden.law.weight (Hidden.latentHistory j) reference.1
        (fun a => CoinProduct.maskedAverage (observed j) reference.2
          (fun signs => f (a, signs))) := by
  classical
  unfold historySum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [raw_history_rel, latent_history_rel, rawLaw, Hidden.law]
  by_cases ha : Hidden.History j reference.1 a
  · simp only [ha, true_and, ite_true, CoinProduct.maskedAverage, CoinProduct.average]
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro signs _
    split_ifs <;> ring
  · simp only [ha, false_and, ite_false, Finset.sum_const_zero]

theorem raw_history_mass (j : ℕ) (reference : Raw) :
    historyMass rawLaw.weight (rawHistory j) reference =
      CoinProduct.mass (observed j) *
        historyMass Hidden.law.weight (Hidden.latentHistory j) reference.1 := by
  unfold historyMass
  rw [raw_history_sum]
  simp_rw [CoinProduct.maskedAverage_one]
  exact FiniteConditioning.historySum_const _ _ _ _

theorem raw_history_latent (j : ℕ) (reference : Raw) (f : Hidden.Atom → ℝ) :
    historySum rawLaw.weight (rawHistory j) reference (fun s => f s.1) =
      CoinProduct.mass (observed j) *
        historySum Hidden.law.weight (Hidden.latentHistory j) reference.1 f := by
  rw [raw_history_sum]
  simp_rw [CoinProduct.maskedAverage_const]
  simpa only [mul_comm] using historySum_scale Hidden.law
    (Hidden.latentHistory j) reference.1 (CoinProduct.mass (observed j)) f

theorem stock_past_adapted (j : ℕ) (a b : Hidden.Atom) (s t : Signs)
    (ha : Hidden.History j a b) (hs : CoinProduct.Agree (observed j) s t) :
    stockValue (Hidden.schedule a) s j = stockValue (Hidden.schedule b) t j := by
  simp_rw [stockValue_eq_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ observed j
  · have hbit := Hidden.history_bit ha i (by simpa [observed] using hi)
    simp only [hi, ite_true, step, hbit, hs i hi]
  · simp only [hi, ite_false]

theorem stock_martingale (j k : ℕ) (hjk : j ≤ k) (reference : Raw) :
    historySum rawLaw.weight (rawHistory j) reference
      (fun s => stockValue (Hidden.schedule s.1) s.2 k) =
      stockValue (Hidden.schedule reference.1) reference.2 j *
        historyMass rawLaw.weight (rawHistory j) reference := by
  rw [raw_history_sum, raw_history_mass]
  simp_rw [stockValue_masked_average _ j k hjk]
  rw [historySum_congr Hidden.law (Hidden.latentHistory j) reference.1
    (fun a => stockValue (Hidden.schedule a) reference.2 j * CoinProduct.mass (observed j))
    (fun _ => stockValue (Hidden.schedule reference.1) reference.2 j *
      CoinProduct.mass (observed j)) (by
      intro a ha
      rw [stock_past_adapted j reference.1 a reference.2 reference.2 ha (fun _ _ => rfl)])]
  rw [FiniteConditioning.historySum_const]
  ring

theorem budget_nonneg (j : ℕ) (h : Fin 7) (a : Hidden.Atom) :
    0 ≤ conditionalBudget j h a :=
  mul_nonneg c_nonneg (avg_nonneg Hidden.law _ _
    (fun b => cellBit_nonneg (Hidden.schedule b) h) a)

theorem budget_le_c (j : ℕ) (h : Fin 7) (a : Hidden.Atom) :
    conditionalBudget j h a ≤ c := by
  have hb := avg_le Hidden.law (Hidden.latentHistory j)
    (fun b => cellBit (Hidden.schedule b) h) 1 zero_le_one
    (fun b => cellBit_le_one _ _) a
  simpa [conditionalBudget] using mul_le_mul_of_nonneg_left hb c_nonneg

theorem budget_zero (j : ℕ) (a : Hidden.Atom) : conditionalBudget j 0 a = 0 := by
  simp [conditionalBudget, cellBit_zero, avg_zero]

theorem conditional_log_step (j : ℕ) (i : Fin 6) (future : j ≤ i.val + 1)
    (reference : Raw) :
    historySum rawLaw.weight (rawHistory j) reference
      (fun s => -2 * Real.log (step (Hidden.schedule s.1) i (s.2 i))) =
      conditionalBudget j i.succ reference.1 *
        historyMass rawLaw.weight (rawHistory j) reference := by
  rw [raw_history_sum, raw_history_mass]
  have mask (a : Hidden.Atom) := CoinProduct.maskedAverage_unseen_single
    (observed j) reference.2 i (by simp [observed]; omega)
    (fun up => -2 * Real.log (step (Hidden.schedule a) i up))
  simp_rw [mask, step_log_average]
  have rearrange :
      (fun a : Hidden.Atom => c * (bit (Hidden.schedule a) i : ℝ) * CoinProduct.mass (observed j)) =
      (fun a => (c * CoinProduct.mass (observed j)) * (bit (Hidden.schedule a) i : ℝ)) := by
    funext a
    ring
  rw [rearrange, historySum_scale, avg_reconstruct]
  simp only [conditionalBudget, cellBit_succ]
  ring

theorem budget_tower (j k : ℕ) (hjk : j ≤ k) (h : Fin 7) (reference : Raw) :
    historySum rawLaw.weight (rawHistory j) reference
      (fun s => conditionalBudget k h s.1) =
      conditionalBudget j h reference.1 *
        historyMass rawLaw.weight (rawHistory j) reference := by
  rw [raw_history_latent, raw_history_mass]
  unfold conditionalBudget
  rw [historySum_scale, avg_tower_hsum Hidden.law (Hidden.latentHistory j)
    (Hidden.latentHistory k) (fun a b hab => Hidden.history_refines hjk hab)]
  ring

def model : FiniteModel grid Raw where
  law := rawLaw
  filtration := filtration
  stock := fun j s => stockValue (Hidden.schedule s.1) s.2 j.val
  budget := fun j h s => conditionalBudget j.val h s.1
  stock_pos := by intro j s; exact stockValue_pos _ _ _
  stock_initial := by intro s; exact stockValue_zero _ _
  stock_adapted := by intro j s t h; exact stock_past_adapted _ _ _ _ _ h.1 h.2
  budget_nonneg := by intro j h s _; exact budget_nonneg _ _ _
  budget_adapted := by
    intro j h s t _ hst
    exact congrArg (fun x => c*x) (avg_adapted Hidden.law
      (Hidden.latentHistory j.val) (fun b => cellBit (Hidden.schedule b) h) hst.1)
  martingale := by intro j k hjk s; exact stock_martingale _ _ hjk _
  diagonal := by
    intro h reference
    refine Fin.cases ?_ (fun i => ?_) h
    · simp [stockValue_one, stockValue_zero, budget_zero, historySum]
    · change historySum rawLaw.weight (rawHistory (i.val+1)) reference
        (fun s => -2 * Real.log (stockValue (Hidden.schedule s.1) s.2 (i.val+2) /
          stockValue (Hidden.schedule s.1) s.2 (i.val+1))) = _
      simp_rw [stockValue_ratio]
      exact conditional_log_step _ i le_rfl reference
  tower := by intro j k h hjk _ s; exact budget_tower _ _ hjk _ _

theorem model_root_budget (i : Fin 6) (s : Raw) : model.budget 0 i.succ s = c/2 := by
  change conditionalBudget 0 i.succ s.1 = _
  simp only [conditionalBudget, cellBit_succ]
  rw [avg_root Hidden.law (Hidden.latentHistory 0) Hidden.history_root]
  change c * (∑ a, Hidden.weight a * (bit (Hidden.schedule a) i : ℝ)) = c/2
  rw [Hidden.bit_mean]
  ring

theorem window_cell_sum (a : Schedule) (w : Fin 3) :
    (∑ h ∈ (window w).cells, cellBit a h) = (windowCount a w : ℝ) := by
  simp only [Window.cells, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases w <;> norm_num [window, cellBit, windowCount, Fin.sum_univ_succ]

theorem window_average (a : Hidden.Atom) (w : Fin 3) :
    conditionalAverage Hidden.law (Hidden.latentHistory (w.val+2))
      (fun b => (windowCount (Hidden.schedule b) w : ℝ)) a = Hidden.signal a w := by
  apply avg_eq_of_history_sum _ _ _ a (latent_mass_pos _ _) _
  have h := Hidden.history_window a w
  have hsub : historySum Hidden.law.weight (Hidden.latentHistory (w.val+2)) a
      (fun b => (windowCount (Hidden.schedule b) w : ℝ) - Hidden.signal a w) = 0 := by
    simpa only [historySum, latent_history_rel, Hidden.law] using h
  have linear : historySum Hidden.law.weight (Hidden.latentHistory (w.val+2)) a
      (fun b => (windowCount (Hidden.schedule b) w : ℝ) - Hidden.signal a w) =
      historySum Hidden.law.weight (Hidden.latentHistory (w.val+2)) a
        (fun b => (windowCount (Hidden.schedule b) w : ℝ)) -
        (Hidden.signal a w : ℝ) * historyMass Hidden.law.weight
          (Hidden.latentHistory (w.val+2)) a := by
    classical
    unfold historyMass historySum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [linear] at hsub
  exact sub_eq_zero.mp hsub

theorem model_windowBudget (w : Fin 3) (s : Raw) :
    model.windowBudget (window w) s = c * (Hidden.signal s.1 w : ℝ) := by
  change (∑ h ∈ (window w).cells, conditionalBudget (w.val+2) h s.1) = _
  simp only [conditionalBudget]
  rw [← Finset.mul_sum, ← avg_finset_sum]
  simp_rw [window_cell_sum]
  rw [window_average]

theorem model_vix (w : Fin 3) (s : Raw) :
    model.vix (window w) s = QuoteContract.countVix c (Hidden.signal s.1 w) := by
  unfold FiniteModel.vix FiniteModel.vixSquared QuoteContract.countVix
  rw [model_windowBudget, window_tenor]

theorem model_window_log_identity (w : Fin 3) (reference : Raw) :
    historySum model.law.weight (model.filtration.partition (window w).start)
      reference (fun s => -2 * Real.log
        (model.stock (window w).finish s / model.stock (window w).start s)) =
      model.windowBudget (window w) reference *
        historyMass model.law.weight (model.filtration.partition (window w).start) reference := by
  change historySum rawLaw.weight (rawHistory (w.val+2)) reference
    (fun s => -2 * Real.log (stockValue (Hidden.schedule s.1) s.2 (w.val+5) /
      stockValue (Hidden.schedule s.1) s.2 (w.val+2))) = _
  simp_rw [window_log_return]
  rw [ScheduleModel.historySum_add, ScheduleModel.historySum_add,
    conditional_log_step (w.val+2) (windowIndex w 0) (by simp [windowIndex]),
    conditional_log_step (w.val+2) (windowIndex w 1) (by simp [windowIndex]),
    conditional_log_step (w.val+2) (windowIndex w 2) (by simp [windowIndex])]
  have cells : model.windowBudget (window w) reference =
      conditionalBudget (w.val+2) (windowIndex w 0).succ reference.1 +
      conditionalBudget (w.val+2) (windowIndex w 1).succ reference.1 +
      conditionalBudget (w.val+2) (windowIndex w 2).succ reference.1 := by
    simp only [FiniteModel.windowBudget, Window.cells, Finset.sum_filter]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    fin_cases w <;> norm_num [model, window, windowIndex] <;> ring
  rw [cells]
  change _ = _ * historyMass rawLaw.weight (rawHistory (w.val+2)) reference
  ring

theorem model_admissible : Broad.Admissible model := by
  refine ⟨?_, ?_, model_root_budget, ?_⟩
  · intro s
    change stockValue (Hidden.schedule s.1) s.2 1 = 1
    exact stockValue_one (Hidden.schedule s.1) s.2
  · intro s
    change conditionalBudget 0 0 s.1 = 0
    exact budget_zero 0 s.1
  · intro s
    have hstock : (∑ j : Fin 8, (|Real.log (stockValue (Hidden.schedule s.1) s.2 j.val)| +
        stockValue (Hidden.schedule s.1) s.2 j.val)) ≤ 8*(6*Real.log 2+729/64) := by
      calc
        _ ≤ ∑ _ : Fin 8, (6*Real.log 2+729/64) := Finset.sum_le_sum (fun j _ =>
          add_le_add (stockValue_log_bound _ _ _) (stockValue_bounds _ _ _).2)
        _ = _ := by simp; ring
    have hb : (∑ pair ∈ futurePairs, conditionalBudget pair.1.val pair.2 s.1) ≤ 28*c := by
      calc
        _ ≤ ∑ _pair ∈ futurePairs, c := Finset.sum_le_sum (fun pair _ => budget_le_c _ _ _)
        _ = _ := by simp [futurePairs_card]
    have hbound : Broad.momentSize model s ≤ momentEnvelope :=
      add_le_add (add_le_add (le_refl 1) hstock) hb
    have hnonneg : 0 ≤ Broad.momentSize model s := by
      unfold Broad.momentSize
      exact add_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ =>
        add_nonneg (abs_nonneg _) (model.stock_pos j s).le)))
        (Finset.sum_nonneg (fun pair _ => budget_nonneg _ _ _))
    exact lt_of_le_of_lt (pow_le_pow_left₀ hnonneg hbound 2) (lt_add_one _)

#print axioms model
#print axioms model_window_log_identity
#print axioms model_admissible

end VixOverlap.HiddenModel
