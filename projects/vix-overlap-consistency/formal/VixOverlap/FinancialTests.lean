import VixOverlap.QuoteContract
import VixOverlap.ScheduleMoments
import VixOverlap.PairTests

/-! The frozen second-moment and overlap tests, with their right-hand sides
expressed using the actual standing SPX model. These are certification tests;
no additional observed budget or joint claim is introduced. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap

open ScheduleCertificate ScheduleModel

theorem quoted_vix_square (n : ℕ) :
    QuoteContract.countVix c n ^ 2 = (c / 3) * (n : ℝ) := by
  unfold QuoteContract.countVix
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg c_nonneg (Nat.cast_nonneg n)) (by norm_num))]
  ring

/-- T2: the quote-implied second moment equals the standing SPX window log
contract divided by the exact tenor three. -/
theorem quoted_second_moment_log_identity (ε : ℝ) (w : Fin 3) :
    (∑ n : Fin 4, mixedTarget ε w n * QuoteContract.countVix c n.val ^ 2) =
      (model uniformScheduleLaw).expectation (fun state => -2 * Real.log
        ((model uniformScheduleLaw).stock (window w).finish state /
          (model uniformScheduleLaw).stock (window w).start state)) / 3 := by
  simp_rw [quoted_vix_square]
  rw [PairTests.vix_squared_mean,
    model_expected_window_log uniformScheduleLaw ScheduleModel.uniform_bit_mean]
  ring

/-- T4: every pair passes the existing overlap test, including every
nonnegative strike. In fact the statement holds for every real strike. -/
theorem quoted_overlap_log_inequality (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (i j : Fin 3) (hij : i < j) (K : ℝ) :
    (∑ n : Fin 4, mixedTarget ε i n *
      max (QuoteContract.countVix c n.val ^ 2 - K) 0) -
    (∑ n : Fin 4, mixedTarget ε j n *
      max (QuoteContract.countVix c n.val ^ 2 - K) 0) ≤
    -(2 / 3 : ℝ) * (model uniformScheduleLaw).expectation (fun state =>
      Real.log ((model uniformScheduleLaw).stock (window j).start state) -
        Real.log ((model uniformScheduleLaw).stock (window i).start state)) := by
  simp_rw [quoted_vix_square]
  rw [model_overlap_log_cost uniformScheduleLaw ScheduleModel.uniform_bit_mean]
  exact PairTests.vix_squared_overlap ε h0 h1 i j hij c K c_nonneg

/-- The separation margin is exact for the entire real-parameter family. -/
theorem exact_separation_margin (ε : ℝ) (hε : ε < 1/30) :
    (∑ t : Fin 3 × Fin 4,
      (windowDual t.1 t.2 : ℝ) * mixedTarget ε t.1 t.2) - 21/32 = (1-30*ε)/32 ∧
    0 < (1-30*ε)/32 := by
  constructor
  · rw [mixed_target_score_value]
    ring
  · linarith

end VixOverlap
