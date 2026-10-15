import VixOverlap.Headline

/-! The unchanged vanilla panel in a broader finite filtered model class.
This file defines the extension target; no existence or impossibility is
assumed. The raw space, filtration, and transition kernel are unrestricted
apart from the explicit structural and common-bound conditions below. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap.Broad

open ScheduleCertificate ScheduleModel

variable {Ω : Type} [Fintype Ω]

def momentSize (M : FiniteModel grid Ω) (state : Ω) : ℝ :=
  1 + (∑ j : Fin 8, (|Real.log (M.stock j state)| + M.stock j state)) +
    ∑ pair ∈ futurePairs, M.budget pair.1 pair.2 state

def Admissible (M : FiniteModel grid Ω) : Prop :=
  (∀ state, M.stock 1 state = 1) ∧
  (∀ state, M.budget 0 0 state = 0) ∧
  (∀ i : Fin 6, ∀ state, M.budget 0 i.succ state = c/2) ∧
  (∀ state, momentSize M state ^ 2 < momentBound)

def FitsPanel (M : FiniteModel grid Ω) (ε : ℝ) (J : Finset (Fin 3)) : Prop :=
  (∀ j : Fin 8, ∀ K : ℝ, 0 ≤ K →
    stockCallPrice M j K = stockCallPrice (model uniformScheduleLaw) j K) ∧
  (∀ w ∈ J, ∀ K : ℝ, 0 ≤ K →
    vixCallPrice M (window w) K = QuoteContract.targetCall c ε w K)

def HasCompatibleLaw (ε : ℝ) : Prop :=
  ∃ (Ω : Type) (inst : Fintype Ω) (M : @FiniteModel 7 grid Ω inst),
    @Admissible Ω inst M ∧ @FitsPanel Ω inst M ε Finset.univ

end VixOverlap.Broad
