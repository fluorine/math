import VixOverlap.HiddenModel
import VixOverlap.QuoteBridge

/-! Ordinary marginal call prices of the hidden-schedule realization.
The latent schedule pushforward is used only to calculate its stock prices;
it is not asserted to be identified as a joint law by vanilla observations. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap.HiddenQuotes

open ScheduleCertificate ScheduleModel

def scheduleWeight (s : Schedule) : ℝ :=
  ∑ a : Hidden.Atom, if Hidden.schedule a = s then Hidden.weight a else 0

theorem schedule_expectation (f : Schedule → ℝ) :
    (∑ a : Hidden.Atom, Hidden.weight a * f (Hidden.schedule a)) =
      ∑ s : Schedule, scheduleWeight s * f s := by
  calc
    _ = ∑ s : Schedule, f s * scheduleWeight s :=
      Vanilla.sum_by_statistic Hidden.weight Hidden.schedule f
    _ = _ := Finset.sum_congr rfl (fun s _ => mul_comm _ _)

theorem schedule_probability : IsProbability scheduleWeight := by
  constructor
  · intro s
    unfold scheduleWeight
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact Hidden.weight_nonneg a
    · exact le_rfl
  · have equal := (schedule_expectation (fun _ => 1)).symm
    simpa only [mul_one, Hidden.weight_total] using equal

theorem schedule_prefix_marginals : PrefixMarginals scheduleWeight := by
  intro j k
  have equal := schedule_expectation
    (fun s => if prefixCount s j = k.val then (1 : ℝ) else 0)
  have atoms : Hidden.atomMass (fun a => prefixCount (Hidden.schedule a) j) k.val =
      ScheduleCertificate.atomMass scheduleWeight (fun s => prefixCount s j) k.val := by
    simpa only [Hidden.atomMass, ScheduleCertificate.atomMass, mul_ite, mul_one,
      mul_zero] using equal
  exact atoms.symm.trans (Hidden.prefix_mass j k)

theorem model_expectation_raw (f : HiddenModel.Raw → ℝ) :
    HiddenModel.model.expectation f =
      ∑ a : Hidden.Atom, Hidden.weight a * CoinProduct.average (fun signs => f (a, signs)) := by
  change (∑ s : HiddenModel.Raw, (Hidden.weight s.1 / 64) * f s) = _
  rw [Fintype.sum_prod_type]
  simp only [CoinProduct.average, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro signs _
  ring

theorem model_expectation_latent (f : Hidden.Atom → ℝ) :
    HiddenModel.model.expectation (fun s => f s.1) =
      ∑ a : Hidden.Atom, Hidden.weight a * f a := by
  rw [model_expectation_raw]
  simp only [CoinProduct.average_const]

theorem model_stock_call_pushforward (j : Fin 8) (K : ℝ) :
    stockCallPrice HiddenModel.model j K = QuoteContract.stockCall scheduleWeight j K := by
  unfold stockCallPrice
  rw [model_expectation_raw]
  change (∑ a : Hidden.Atom, Hidden.weight a * CoinProduct.average
    (fun signs => callPayoff K (stockValue (Hidden.schedule a) signs j.val))) = _
  exact schedule_expectation
    (fun s => CoinProduct.average (fun signs => callPayoff K (stockValue s signs j.val)))

/-- Every standing stock call, at every event and every real strike, agrees
with the unchanged uniform-schedule baseline. -/
theorem model_stock_calls (j : Fin 8) (K : ℝ) :
    stockCallPrice HiddenModel.model j K =
      stockCallPrice (ScheduleModel.model uniformScheduleLaw) j K := by
  rw [model_stock_call_pushforward, actual_stock_call]
  exact QuoteContract.prefix_force_stock_calls scheduleWeight schedule_probability
    schedule_prefix_marginals j K

/-- Signal marginals become ordinary VIX call prices only after the filtered
model proves its VIX value equals the square root of the conditional budget. -/
theorem model_vix_calls (w : Fin 3) (K : ℝ) :
    vixCallPrice HiddenModel.model (window w) K = QuoteContract.targetCall c 0 w K := by
  classical
  unfold vixCallPrice
  simp_rw [HiddenModel.model_vix]
  rw [model_expectation_latent
    (fun a => callPayoff K (QuoteContract.countVix c (Hidden.signal a w)))]
  let X : Hidden.Atom → Fin 4 := fun a =>
    ⟨Hidden.signal a w, Hidden.signal_lt_four a w⟩
  have equal := Vanilla.sum_by_statistic Hidden.weight X
    (fun n => callPayoff K (QuoteContract.countVix c n.val))
  change (∑ a : Hidden.Atom, Hidden.weight a *
    callPayoff K (QuoteContract.countVix c (Hidden.signal a w))) = _ at equal
  rw [equal]
  unfold QuoteContract.targetCall
  apply Finset.sum_congr rfl
  intro n _
  have atoms : (∑ a : Hidden.Atom, if X a = n then Hidden.weight a else 0) = target w n := by
    simpa only [X, Fin.ext_iff, Hidden.atomMass] using Hidden.signal_mass w n
  rw [atoms]
  simp only [mixedTarget, sub_zero, one_mul, zero_mul, add_zero]
  exact mul_comm _ _

theorem model_fitsPanel : Broad.FitsPanel HiddenModel.model 0 Finset.univ := by
  constructor
  · intro j K _
    exact model_stock_calls j K
  · intro w _ K _
    exact model_vix_calls w K

/-- The same complete vanilla panel at epsilon zero admits an actual finite
filtered model in the broader class, with its original root budgets and bound. -/
theorem zero_compatible : Broad.HasCompatibleLaw 0 :=
  ⟨HiddenModel.Raw, inferInstance, HiddenModel.model,
    HiddenModel.model_admissible, model_fitsPanel⟩

end VixOverlap.HiddenQuotes
