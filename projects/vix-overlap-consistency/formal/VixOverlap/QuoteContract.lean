import VixOverlap.ScheduleStock
import VixOverlap.ScheduleCertificate
import VixOverlap.Vanilla
import Mathlib.Analysis.Real.Sqrt

/-! The proposed financial statement, written before its proof. These are
ordinary payoff definitions and a proposition, not an assumed result. The
separate ScheduleModel construction must prove the full filtered realization. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap.QuoteContract

open ScheduleCertificate ScheduleModel

def stockCall (p : Schedule → ℝ) (j : Fin 8) (K : ℝ) : ℝ :=
  ∑ a, p a * CoinProduct.average (fun e => callPayoff K (stockValue a e j.val))

def countVix (c : ℝ) (n : ℕ) : ℝ := Real.sqrt (c * n / 3)

def windowCall (c : ℝ) (p : Schedule → ℝ) (w : Fin 3) (K : ℝ) : ℝ :=
  ∑ a, p a * callPayoff K (countVix c (windowCount a w))

def targetCall (c ε : ℝ) (w : Fin 3) (K : ℝ) : ℝ :=
  ∑ n : Fin 4, mixedTarget ε w n * callPayoff K (countVix c n.val)

/-- Every calibration constraint here is an ordinary marginal call constraint.
Cash normalization is included in IsProbability. Latent count marginals are
deliberately absent from the hypothesis. -/
def Calibrates (c ε : ℝ) (p : Schedule → ℝ) (J : Finset (Fin 3)) : Prop :=
  IsProbability p ∧
  (∀ j : Fin 8, ∀ K : ℝ, 0 ≤ K → stockCall p j K = stockCall uniformWeight j K) ∧
  (∀ w ∈ J, ∀ K : ℝ, 0 ≤ K → windowCall c p w K = targetCall c ε w K)

/-- The complete quote claim: all proper subpanels and impossibility for all
three, quantified over arbitrary real probability weights on the SAME class.
The empty subpanel is included harmlessly; all nonempty proper panels follow. -/
def ThreeWindowObstruction (c ε : ℝ) : Prop :=
  (∀ J : Finset (Fin 3), J.card ≤ 2 → ∃ p : Schedule → ℝ, Calibrates c ε p J) ∧
  ¬ (∃ p : Schedule → ℝ, Calibrates c ε p Finset.univ)

end VixOverlap.QuoteContract
