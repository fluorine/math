import VixOverlap.HiddenQuotes
import VixOverlap.Mixture

/-! The same ordinary vanilla panel is compatible when the early-revealed
activity architecture is relaxed. The construction keeps the stock dynamics,
root budgets, time grid, tenor, and common moment bound. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap.Extension

open ScheduleCertificate ScheduleModel

abbrev Raw := HiddenModel.Raw ⊕ ScheduleModel.State

theorem raw_card : Fintype.card Raw = 6592 := by
  simp [Raw, HiddenModel.Raw, ScheduleModel.State, ScheduleModel.Signs,
    CoinProduct.Signs, Hidden.Atom, Schedule]

/-- Two positive latent states are still indistinguishable at the first
fixing, although the eventual active-cell counts in its window differ. -/
theorem hidden_window_not_revealed :
    ∃ a b : Hidden.Atom,
      0 < Hidden.weight a ∧ 0 < Hidden.weight b ∧ Hidden.History 2 a b ∧
      windowCount (Hidden.schedule a) 0 ≠ windowCount (Hidden.schedule b) 0 := by
  exact ⟨0, 4, Hidden.weight_pos 0, Hidden.weight_pos 4, by decide, by decide⟩

/-- A fixed carrier for the entire parameter family, including endpoints. -/
def model (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : FiniteModel grid Raw :=
  Broad.mix HiddenModel.model (ScheduleModel.model uniformScheduleLaw) ε h0 h1
    HiddenModel.model_admissible Broad.uniform_admissible

theorem model_admissible (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Broad.Admissible (model ε h0 h1) :=
  Broad.mix_admissible _ _ _ _ _ _ _

theorem model_fitsPanel (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Broad.FitsPanel (model ε h0 h1) ε Finset.univ :=
  Broad.mix_fitsPanel _ _ _ _ _ _ _ _ HiddenQuotes.model_fitsPanel
    (Broad.uniform_fitsPanel Finset.univ)

theorem model_window_log_identity (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (w : Fin 3) (x : Raw) :
    let M := model ε h0 h1
    historySum M.law.weight (M.filtration.partition (window w).start) x
      (fun y => -2 * Real.log (M.stock (window w).finish y / M.stock (window w).start y)) =
      M.windowBudget (window w) x *
        historyMass M.law.weight (M.filtration.partition (window w).start) x :=
  Broad.mix_window_log_identity _ _ ε h0 h1 _ _
    HiddenModel.model_window_log_identity
    (ScheduleModel.model_window_log_identity uniformScheduleLaw) w x

/-- The full financial existence claim: one fixed finite carrier, all ordinary
calls, unchanged root conditions and bound, unit stock forwards, and the
idealized conditional-log VIX identity at every fixing/history. -/
theorem financial_same_panel_compatibility (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ M : FiniteModel grid Raw,
      Broad.Admissible M ∧ Broad.FitsPanel M ε Finset.univ ∧
      (∀ j : Fin 8, M.expectation (M.stock j) = 1) ∧
      (∀ w : Fin 3, ∀ x : Raw,
        historySum M.law.weight (M.filtration.partition (window w).start) x
          (fun y => -2 * Real.log
            (M.stock (window w).finish y / M.stock (window w).start y)) =
          M.windowBudget (window w) x *
            historyMass M.law.weight (M.filtration.partition (window w).start) x) := by
  exact ⟨model ε h0 h1, model_admissible ε h0 h1, model_fitsPanel ε h0 h1,
    Mixture.root_stock_expectation (model ε h0 h1), model_window_log_identity ε h0 h1⟩

/-- Constructive compatibility of every quoted family member, including all
parameters excluded by the early-revealed architecture theorem. -/
theorem same_panel_compatible (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Broad.HasCompatibleLaw ε :=
  ⟨Raw, inferInstance, model ε h0 h1, model_admissible ε h0 h1,
    model_fitsPanel ε h0 h1⟩

/-- The old incompatibility does not survive removal of the information
restriction. Both conclusions use exactly the same ordinary-call targets. -/
theorem information_restriction_is_essential (ε : ℝ) (h0 : 0 ≤ ε)
    (hε : ε < 1/30) :
    (¬ ∃ p : FiniteLaw Schedule, FitsVanilla p ε Finset.univ) ∧
      Broad.HasCompatibleLaw ε := by
  exact ⟨(financial_three_window_obstruction ε h0 hε).2.1,
    same_panel_compatible ε h0 (by linarith)⟩

end VixOverlap.Extension
