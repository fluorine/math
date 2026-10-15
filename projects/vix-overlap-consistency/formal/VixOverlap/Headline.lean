import VixOverlap.QuoteBridge
import VixOverlap.ScheduleBounds
import VixOverlap.BudgetAlgebra
import VixOverlap.FinancialTests

/-! Integrated financial claim for the explicitly finite, early-revealed
activity-schedule architecture. No unrestricted-market claim is made. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap

open ScheduleCertificate ScheduleModel

/-- The observable panel uses the calls of the actual constructed structural
model. All standing SPX calls remain fixed when a VIX window is deleted. -/
def FitsVanilla (p : FiniteLaw Schedule) (ε : ℝ) (J : Finset (Fin 3)) : Prop :=
  (∀ j : Fin 8, ∀ K : ℝ, 0 ≤ K →
    stockCallPrice (model p) j K = stockCallPrice (model uniformScheduleLaw) j K) ∧
  (∀ w ∈ J, ∀ K : ℝ, 0 ≤ K →
    vixCallPrice (model p) (window w) K = QuoteContract.targetCall c ε w K)

theorem actual_stock_call (p : FiniteLaw Schedule) (j : Fin 8) (K : ℝ) :
    stockCallPrice (model p) j K = QuoteContract.stockCall p.weight j K := by
  exact (QuoteContract.stockCall_eq_raw p.weight j K).symm

theorem actual_vix_call (p : FiniteLaw Schedule) (w : Fin 3) (K : ℝ) :
    vixCallPrice (model p) (window w) K = QuoteContract.windowCall c p.weight w K := by
  unfold vixCallPrice FiniteModel.expectation
  simp_rw [model_vix]
  exact QuoteContract.raw_schedule_expectation p.weight
    (fun a => callPayoff K (QuoteContract.countVix c (windowCount a w)))

theorem fitsVanilla_iff (p : FiniteLaw Schedule) (ε : ℝ) (J : Finset (Fin 3)) :
    FitsVanilla p ε J ↔ QuoteContract.Calibrates c ε p.weight J := by
  have hp : IsProbability p.weight := ⟨p.nonneg, p.total⟩
  simp only [FitsVanilla, QuoteContract.Calibrates, actual_stock_call,
    actual_vix_call, show uniformScheduleLaw.weight = uniformWeight from rfl,
    hp, true_and]

/-- All three tenor-three windows share the same risky cell [4,5]. -/
theorem genuinely_overlapping (w : Fin 3) :
    (window w).tenor grid = 3 ∧ (4 : Fin 7) ∈ (window w).cells := by
  refine ⟨window_tenor w, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change w.val + 2 ≤ 4 ∧ 4 < w.val + 5
  omega

/-- Standing ordinary SPX calls force the same root budget field in every
calibrating schedule law; these budgets are not additional observed claims. -/
theorem fitting_root_budgets (p : FiniteLaw Schedule) (ε : ℝ) (J : Finset (Fin 3))
    (hfit : FitsVanilla p ε J) (i : Fin 6) (s : State) :
    (model p).budget 0 i.succ s = c/2 := by
  have hs := ((fitsVanilla_iff p ε J).mp hfit).2.1
  exact model_root_budget p
    (prefix_marginals_bit_mean p.weight (QuoteContract.stock_calls_force_prefix p.weight hs)) i s

/-- Complete finite-architecture theorem. Every proper subpanel has an actual
filtered positive-SPX model with full diagonal and tower rows, common initial
budgets and one common moment bound. The full panel has no law anywhere in the
same real-weight schedule class. All conditional log rows are unnormalized.

This is model inconsistency within the declared architecture, not an executable
arbitrage or an unrestricted continuous-market impossibility theorem. -/
theorem financial_three_window_obstruction (ε : ℝ) (h0 : 0 ≤ ε) (hε : ε < 1/30) :
    (∀ J : Finset (Fin 3), J.card ≤ 2 → ∃ p : FiniteLaw Schedule,
      FitsVanilla p ε J ∧
      (∀ i : Fin 6, ∀ s : State, (model p).budget 0 i.succ s = c/2) ∧
      (0 < ε → ∀ s : State, 0 < (model p).law.weight s) ∧
      (∀ s : State, gamma p s ^ 2 < momentBound) ∧
      (∀ w : Fin 3, ∀ s : State,
        historySum (model p).law.weight ((model p).filtration.partition (window w).start)
          s (fun z => -2 * Real.log
            ((model p).stock (window w).finish z / (model p).stock (window w).start z)) =
        (model p).windowBudget (window w) s *
          historyMass (model p).law.weight
            ((model p).filtration.partition (window w).start) s)) ∧
    (¬ (∃ p : FiniteLaw Schedule, FitsVanilla p ε Finset.univ)) ∧
    (∀ w : Fin 3,
      (∑ n : Fin 4, mixedTarget ε w n * QuoteContract.countVix c n.val ^ 2) =
        (model uniformScheduleLaw).expectation (fun state => -2 * Real.log
          ((model uniformScheduleLaw).stock (window w).finish state /
            (model uniformScheduleLaw).stock (window w).start state)) / 3) ∧
    (∀ i j : Fin 3, i < j → ∀ K : ℝ,
      (∑ n : Fin 4, mixedTarget ε i n * max (QuoteContract.countVix c n.val ^ 2 - K) 0) -
      (∑ n : Fin 4, mixedTarget ε j n * max (QuoteContract.countVix c n.val ^ 2 - K) 0) ≤
      -(2 / 3 : ℝ) * (model uniformScheduleLaw).expectation (fun state =>
        Real.log ((model uniformScheduleLaw).stock (window j).start state) -
          Real.log ((model uniformScheduleLaw).stock (window i).start state))) ∧
    ((∑ t : Fin 3 × Fin 4,
      (windowDual t.1 t.2 : ℝ) * mixedTarget ε t.1 t.2) - 21/32 = (1-30*ε)/32 ∧
      0 < (1-30*ε)/32) := by
  have h1 : ε ≤ 1 := by linarith
  constructor
  · intro J hJ
    obtain ⟨b, hb⟩ := proper_panel_contained_in_pair J hJ
    have hp := mixed_probability ε h0 h1 b
    let p : FiniteLaw Schedule := ⟨mixedWeight ε b, hp.1, hp.2⟩
    have hcal : QuoteContract.Calibrates c ε p.weight J := by
      refine ⟨hp, ?_, ?_⟩
      · intro j K _
        exact QuoteContract.prefix_force_stock_calls _ hp (mixed_prefix ε b) j K
      · intro w hw K _
        exact QuoteContract.windowCall_from_marginal c ε _ w
          (mixed_window ε b w (hb w hw)) K
    have hfit : FitsVanilla p ε J := (fitsVanilla_iff p ε J).mpr hcal
    refine ⟨p, hfit, fitting_root_budgets p ε J hfit, ?_,
      uniform_moment_bound p, model_window_log_identity p⟩
    intro hpos s
    exact div_pos (mixed_strictly_positive ε hpos h1 b s.1) (by norm_num)
  · refine ⟨?_, quoted_second_moment_log_identity ε, ?_, exact_separation_margin ε hε⟩
    · rintro ⟨p, hp⟩
      exact (QuoteContract.vanilla_three_window_obstruction c_pos ε h0 hε).2
        ⟨p.weight, (fitsVanilla_iff p ε Finset.univ).mp hp⟩
    · intro i j hij K
      exact quoted_overlap_log_inequality ε h0 h1 i j hij K

end VixOverlap
