import Snaky.E1Conditions
import Snaky.E1Uncovered

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncoveredFor_exact (p m : Nat) :
    sources.filter (fun t => !covered (pairsFor p m) t) = uncoveredFor p m := by
  cases p with
  | zero =>
    cases m with
    | zero => exact uncovered00_exact
    | succ m => cases m with
      | zero => exact uncovered01_exact
      | succ m => exact uncovered02_exact
  | succ p =>
    cases m with
    | zero => exact uncovered10_exact
    | succ m => cases m with
      | zero => exact uncovered11_exact
      | succ m => exact uncovered12_exact



end Snaky.E1
