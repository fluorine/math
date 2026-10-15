import VixOverlap.Model
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators

namespace VixOverlap.FiniteModel

variable {N : ℕ} {grid : EventGrid N} {Ω : Type*} [Fintype Ω]

/-- Integrated future-cell budgets at one fixed valuation date. Additivity
concerns the future interval, while the conditioning date stays fixed. -/
def intervalBudget (M : FiniteModel grid Ω) (j i k : Fin (N+1)) (ω : Ω) : ℝ :=
  ∑ h : Fin N, if i.val ≤ h.val ∧ h.val < k.val then M.budget j h ω else 0

theorem intervalBudget_additive (M : FiniteModel grid Ω)
    (j i m k : Fin (N+1)) (him : i ≤ m) (hmk : m ≤ k) (ω : Ω) :
    M.intervalBudget j i k ω = M.intervalBudget j i m ω + M.intervalBudget j m k ω := by
  simp only [intervalBudget, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  have h1 : i.val ≤ m.val := him
  have h2 : m.val ≤ k.val := hmk
  split_ifs <;> first | omega | simp_all

theorem intervalBudget_nonneg (M : FiniteModel grid Ω)
    (j i k : Fin (N+1)) (hji : j ≤ i) (ω : Ω) :
    0 ≤ M.intervalBudget j i k ω := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs with hcell
  · exact M.budget_nonneg j h ω (by have : j.val ≤ i.val := hji; omega)
  · exact le_rfl

theorem windowBudget_eq_intervalBudget (M : FiniteModel grid Ω)
    (w : Window N) (ω : Ω) :
    M.windowBudget w ω = M.intervalBudget w.start w.start w.finish ω := by
  simp [windowBudget, Window.cells, intervalBudget, Finset.sum_filter]

end VixOverlap.FiniteModel
