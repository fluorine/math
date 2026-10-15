import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import VixOverlap.Payoff

/-!
# Finite filtered conditional-log-variance models

These are structural definitions, not a claim that arbitrary overlapping-window
quotes are feasible. All conditional equations are multiplied by history mass.
In particular, an empty history imposes the identity `0 = 0`.

Cell `h : Fin N` is the interval from event `h.castSucc` to `h.succ`.
`budget j h` is an integrated variance budget, so annualized VIX squared divides
the window sum by its elapsed time in years. VIX is in volatility units, without
the conventional factor of 100 used for index points.
-/

noncomputable section

open scoped BigOperators

namespace VixOverlap

/-- Event dates in years, fixed independently of any law or quote subpanel. -/
structure EventGrid (N : ℕ) where
  time : Fin (N + 1) → ℝ
  increasing : StrictMono time

/-- Arbitrary finite probability weights. Zero-weight states are permitted. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

/-- A finite filtration encoded by equivalence relations on full histories.
The terminal relation is unrestricted: this also permits latent terminal states.
-/
structure HistoryFiltration (N : ℕ) (Ω : Type*) where
  partition : Fin (N + 1) → Setoid Ω
  refines : ∀ j k, j ≤ k → ∀ ω η,
    (partition k).r ω η → (partition j).r ω η
  root : ∀ ω η, (partition 0).r ω η

/-- Unnormalized expectation restricted to the history of a representative. -/
def historySum {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (H : Setoid Ω)
    (ω : Ω) (f : Ω → ℝ) : ℝ := by
  classical
  exact ∑ η, if H.r ω η then p η * f η else 0

def historyMass {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (H : Setoid Ω)
    (ω : Ω) : ℝ := historySum p H ω (fun _ => 1)

/-- A positive discounted-stock model with its entire budget array.
Only coordinates with `j.val ≤ h.val` describe future variance budgets.
All structural equations persist when observable quote constraints are removed.
-/
structure FiniteModel {N : ℕ} (grid : EventGrid N) (Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  filtration : HistoryFiltration N Ω
  stock : Fin (N + 1) → Ω → ℝ
  budget : Fin (N + 1) → Fin N → Ω → ℝ
  stock_pos : ∀ j ω, 0 < stock j ω
  stock_initial : ∀ ω, stock 0 ω = 1
  stock_adapted : ∀ j ω η,
    (filtration.partition j).r ω η → stock j ω = stock j η
  budget_nonneg : ∀ j h ω, j.val ≤ h.val → 0 ≤ budget j h ω
  budget_adapted : ∀ j h ω η, j.val ≤ h.val →
    (filtration.partition j).r ω η → budget j h ω = budget j h η
  martingale : ∀ j k, j ≤ k → ∀ ω,
    historySum law.weight (filtration.partition j) ω (stock k) =
      stock j ω * historyMass law.weight (filtration.partition j) ω
  diagonal : ∀ h ω,
    historySum law.weight (filtration.partition h.castSucc) ω
        (fun η => -2 * Real.log (stock h.succ η / stock h.castSucc η)) =
      budget h.castSucc h ω *
        historyMass law.weight (filtration.partition h.castSucc) ω
  tower : ∀ j k h, j ≤ k → k.val ≤ h.val → ∀ ω,
    historySum law.weight (filtration.partition j) ω (budget k h) =
      budget j h ω * historyMass law.weight (filtration.partition j) ω

/-- A nonempty window on the fixed event grid. -/
structure Window (N : ℕ) where
  start : Fin (N + 1)
  finish : Fin (N + 1)
  nonempty : start < finish

namespace Window

def cells {N : ℕ} (w : Window N) : Finset (Fin N) :=
  Finset.univ.filter (fun h => w.start.val ≤ h.val ∧ h.val < w.finish.val)

def tenor {N : ℕ} (grid : EventGrid N) (w : Window N) : ℝ :=
  grid.time w.finish - grid.time w.start

theorem tenor_pos {N : ℕ} (grid : EventGrid N) (w : Window N) :
    0 < w.tenor grid := sub_pos.mpr (grid.increasing w.nonempty)

end Window

namespace FiniteModel

variable {N : ℕ} {grid : EventGrid N} {Ω : Type*} [Fintype Ω]

def expectation (M : FiniteModel grid Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, M.law.weight ω * f ω

def windowBudget (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) : ℝ :=
  ∑ h ∈ w.cells, M.budget w.start h ω

def vixSquared (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) : ℝ :=
  M.windowBudget w ω / w.tenor grid

def vix (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) : ℝ :=
  Real.sqrt (M.vixSquared w ω)

theorem windowBudget_nonneg (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) :
    0 ≤ M.windowBudget w ω := by
  apply Finset.sum_nonneg
  intro h hh
  exact M.budget_nonneg w.start h ω (Finset.mem_filter.mp hh).2.1

theorem vixSquared_nonneg (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) :
    0 ≤ M.vixSquared w ω :=
  div_nonneg (M.windowBudget_nonneg w ω) (w.tenor_pos grid).le

/-- The exact VIX-squared normalization, with positive tenor proved. -/
theorem vix_sq (M : FiniteModel grid Ω) (w : Window N) (ω : Ω) :
    M.vix w ω ^ 2 = M.windowBudget w ω / w.tenor grid :=
  Real.sq_sqrt (M.vixSquared_nonneg w ω)

end FiniteModel

def stockCallPrice {N : ℕ} {grid : EventGrid N} {Ω : Type*} [Fintype Ω]
    (M : FiniteModel grid Ω) (j : Fin (N + 1)) (strike : ℝ) : ℝ :=
  M.expectation (fun ω => callPayoff strike (M.stock j ω))

def vixCallPrice {N : ℕ} {grid : EventGrid N} {Ω : Type*} [Fintype Ω]
    (M : FiniteModel grid Ω) (w : Window N) (strike : ℝ) : ℝ :=
  M.expectation (fun ω => callPayoff strike (M.vix w ω))

/-- A nonvacuity witness for the structural class on every grid: cash stock,
zero variance, and the unique state. This is only a supporting example.
-/
def constantModel {N : ℕ} (grid : EventGrid N) : FiniteModel grid PUnit where
  law := {
    weight := fun _ => 1
    nonneg := by intro; exact zero_le_one
    total := by simp
  }
  filtration := {
    partition := fun _ => ⊤
    refines := by intro _ _ _ _ _ _; trivial
    root := by intro _ _; trivial
  }
  stock := fun _ _ => 1
  budget := fun _ _ _ => 0
  stock_pos := by intro _ _; exact zero_lt_one
  stock_initial := by intro; rfl
  stock_adapted := by intro _ _ _ _; rfl
  budget_nonneg := by intro _ _ _ _; exact le_rfl
  budget_adapted := by intro _ _ _ _ _ _; rfl
  martingale := by intros; simp [historySum, historyMass]
  diagonal := by intros; simp [historySum, historyMass]
  tower := by intros; simp [historySum, historyMass]

theorem structural_class_nonempty {N : ℕ} (grid : EventGrid N) :
    Nonempty (FiniteModel grid PUnit) := ⟨constantModel grid⟩

end VixOverlap
