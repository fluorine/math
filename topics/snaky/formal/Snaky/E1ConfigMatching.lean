import Snaky.E1Conditions
import Snaky.E1Matching

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every selected template is a disjoint collection of legal physical pairs. -/
theorem config_matching (mask mode : Nat) :
    (((config mask mode).pairs.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ (config mask mode).pairs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by
  change ((pairsFor (phase mask) mode).flatMap fun p => [p.1, p.2]).Nodup ∧
    (∀ p ∈ pairsFor (phase mask) mode, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2)
  generalize phase mask = phaseValue
  cases phaseValue with
  | zero =>
    cases mode with
    | zero => exact pairs00_matching
    | succ m => cases m with
      | zero => exact pairs01_matching
      | succ m => exact pairs02_matching
  | succ p =>
    cases mode with
    | zero => exact pairs10_matching
    | succ m => cases m with
      | zero => exact pairs11_matching
      | succ m => exact pairs12_matching



end Snaky.E1
