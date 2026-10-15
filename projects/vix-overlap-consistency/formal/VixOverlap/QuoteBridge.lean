import VixOverlap.QuoteContract
import VixOverlap.PriceIdentification
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators

namespace VixOverlap.QuoteContract

open ScheduleCertificate ScheduleModel

def rawWeight (p : Schedule → ℝ) (s : State) : ℝ := p s.1 / 64

theorem raw_schedule_expectation (p f : Schedule → ℝ) :
    (∑ s : State, rawWeight p s * f s.1) = ∑ a, p a * f a := by
  simp [rawWeight, Fintype.sum_prod_type, Fintype.card_fun, Signs, CoinProduct.Signs]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem stockCall_eq_raw (p : Schedule → ℝ) (j : Fin 8) (K : ℝ) :
    stockCall p j K = Vanilla.callSum (rawWeight p)
      (fun s : State => stockValue s.1 s.2 j.val) K := by
  simp only [stockCall, Vanilla.callSum, Fintype.sum_prod_type,
    rawWeight, CoinProduct.average, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem stock_calls_force_prefix (p : Schedule → ℝ)
    (hc : ∀ j : Fin 8, ∀ K : ℝ, 0 ≤ K →
      stockCall p j K = stockCall uniformWeight j K) : PrefixMarginals p := by
  classical
  intro k n
  let j : Fin 8 := ⟨k.val+1, by omega⟩
  have he := Vanilla.calls_identify_fiber_statistic
    (rawWeight p) (rawWeight uniformWeight)
    (fun s : State => stockValue s.1 s.2 (k.val+1))
    (fun s : State => if prefixCount s.1 k = n.val then (1:ℝ) else 0)
    (fun s => stockValue_pos s.1 s.2 _)
    (by
      intro s t h
      have hh : prefixCount s.1 k = prefixCount t.1 k :=
        Vanilla.active_count_identified _ _ _ _
          (by simpa only [stockValue_formula] using h)
      simp only [hh])
    (by
      intro K hK
      simpa only [stockCall_eq_raw, j] using hc j K hK)
  rw [raw_schedule_expectation p (fun a => if prefixCount a k = n.val then (1:ℝ) else 0),
    raw_schedule_expectation uniformWeight
      (fun a => if prefixCount a k = n.val then (1:ℝ) else 0)] at he
  have hm : atomMass p (fun a => prefixCount a k) n.val =
      atomMass uniformWeight (fun a => prefixCount a k) n.val := by
    simpa [atomMass, mul_ite] using he
  exact hm.trans (uniform_prefix k n)

theorem prefix_force_stock_calls (p : Schedule → ℝ) (hp : IsProbability p)
    (hm : PrefixMarginals p) :
    ∀ j : Fin 8, ∀ K : ℝ, stockCall p j K = stockCall uniformWeight j K := by
  classical
  intro j K
  by_cases hj : j.val = 0
  · simp only [stockCall, hj, stockValue_zero, CoinProduct.average_const,
      ← Finset.sum_mul, hp.2, uniform_probability.2]
  · let k : Fin 7 := ⟨j.val-1, by omega⟩
    have hjk : j.val = k.val+1 := by dsimp [k]; omega
    simp only [stockCall, hjk]
    apply Vanilla.masses_identify_fiber_statistic p uniformWeight
      (fun a => (⟨prefixCount a k, by have := prefixCount_le_six a k; omega⟩ : Fin 7))
    · intro a b hab
      exact uniform_stock_function_eq_of_prefixCount_eq a b k
        (congrArg Fin.val hab) (callPayoff K)
    · intro n
      simp only [Fin.ext_iff]
      exact (hm k n).trans (uniform_prefix k n).symm

theorem countVix_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (countVix c) := by
  intro n m h
  have hn : 0 ≤ c*(n:ℝ)/3 := by positivity
  have hm : 0 ≤ c*(m:ℝ)/3 := by positivity
  have hs := congrArg (fun x : ℝ => x^2) h
  simp only [countVix, Real.sq_sqrt hn, Real.sq_sqrt hm] at hs
  have hs' : c * (n:ℝ) = c * (m:ℝ) := by linarith
  have he : (n:ℝ) = (m:ℝ) := mul_left_cancel₀ (ne_of_gt hc) hs'
  exact_mod_cast he

theorem windowCall_from_marginal (c ε : ℝ) (p : Schedule → ℝ) (w : Fin 3)
    (hm : WindowMarginal p w ε) (K : ℝ) :
    windowCall c p w K = targetCall c ε w K := by
  classical
  let X : Schedule → Fin 4 := fun a =>
    ⟨windowCount a w, by have := windowCount_le_three a w; omega⟩
  have he := Vanilla.sum_by_statistic p X
    (fun n => callPayoff K (countVix c n.val))
  change windowCall c p w K = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro n _
  have hm' : (∑ a, if X a = n then p a else 0) = mixedTarget ε w n := by
    simpa only [X, Fin.ext_iff, atomMass] using hm n
  rw [hm']
  ring

private def pairFor (w : Fin 3) : Fin 3 := if w.val = 2 then 1 else 0

private theorem pairFor_contains (w : Fin 3) : pairContains (pairFor w) w := by
  unfold pairFor pairContains
  split_ifs <;> simp_all <;> omega

theorem window_calls_force_marginal {c : ℝ} (hc : 0 < c)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (p : Schedule → ℝ)
    (hp : IsProbability p) (w : Fin 3)
    (hq : ∀ K : ℝ, 0 ≤ K → windowCall c p w K = targetCall c ε w K) :
    WindowMarginal p w ε := by
  classical
  let q := mixedWeight ε (pairFor w)
  have qp : IsProbability q := mixed_probability ε h0 h1 _
  have qm : WindowMarginal q w ε := mixed_window ε _ w (pairFor_contains w)
  intro n
  have he := Vanilla.nonneg_calls_identify_fiber_statistic p q
    (fun a => countVix c (windowCount a w))
    (fun a => if windowCount a w = n.val then (1:ℝ) else 0)
    (fun a => Real.sqrt_nonneg _)
    (hp.2.trans qp.2.symm)
    (by
      intro a b hab
      have hn := countVix_injective hc hab
      simp only [hn])
    (by
      intro K hK
      exact (hq K hK).trans (windowCall_from_marginal c ε q w qm K).symm)
  have hm : atomMass p (fun a => windowCount a w) n.val =
      atomMass q (fun a => windowCount a w) n.val := by
    simpa [atomMass, mul_ite] using he
  exact hm.trans (qm n)

/-- The complete ordinary-vanilla quote obstruction in the declared schedule
architecture. The full structural realization is supplied separately and then
included in the integrated headline theorem. -/
theorem vanilla_three_window_obstruction {c : ℝ} (hc : 0 < c)
    (ε : ℝ) (h0 : 0 ≤ ε) (hε : ε < 1/30) : ThreeWindowObstruction c ε := by
  have h1 : ε ≤ 1 := by linarith
  constructor
  · intro J hJ
    obtain ⟨p, hp, hs, hv⟩ := proper_panel_feasible ε h0 h1 J hJ
    refine ⟨p, hp, ?_, ?_⟩
    · intro j K _
      exact prefix_force_stock_calls p hp hs j K
    · intro w hw K _
      exact windowCall_from_marginal c ε p w (hv w hw) K
  · rintro ⟨p, hp, hs, hv⟩
    apply no_three_window_law ε hε
    refine ⟨p, hp, stock_calls_force_prefix p hs, ?_⟩
    intro w
    exact window_calls_force_marginal hc ε h0 h1 p hp w
      (fun K hK => hv w (Finset.mem_univ _) K hK)

end VixOverlap.QuoteContract
