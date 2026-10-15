module

public import TetrahedronCover.Continuum
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Effective counts and a quantitative two-sided asymptotic remainder.
The estimates concern the actual finite cost defined in Continuum. -/
@[expose] public section
namespace TetrahedronCover
noncomputable section

/-- The prescribed number of cells; the geometric construction uses twice this count. -/
def scheduleCount (e : ℝ) : ℕ := ⌈2/e^2⌉₊

theorem scheduleCount_pos {e : ℝ} (he : 0 < e) : 0 < scheduleCount e := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by norm_num) (sq_pos_of_pos he)

theorem width_le_square {e : ℝ} (he : 0 < e) {N : ℕ} (hN : 0 < N)
    (hcount : scheduleCount e ≤ N) : 2/(N : ℝ) ≤ e^2 := by
  have hc : 2/e^2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hcount)
  have hh := (div_le_iff₀ (sq_pos_of_pos he)).mp hc
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  nlinarith only [hh]

theorem schedule_width_lower {e : ℝ} (he : 0 < e) :
    e^2-e^4/2 ≤ 2/(scheduleCount e : ℝ) := by
  have hn : (0 : ℝ) < (scheduleCount e : ℝ) :=
    Nat.cast_pos.mpr (scheduleCount_pos he)
  have hs := sq_pos_of_pos he
  have hu := width_le_square he (scheduleCount_pos he) (le_refl _)
  have hceil : (scheduleCount e : ℝ) ≤ 2/e^2+1 :=
    (Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) hs))).le
  have hmul := mul_le_mul_of_nonneg_right hceil hs.le
  have hcancel : (2/e^2)*e^2 = (2 : ℝ) := div_mul_cancel₀ _ hs.ne'
  have hnupper : (scheduleCount e : ℝ)*e^2 ≤ 2+e^2 := by
    nlinarith only [hmul, hcancel]
  have hd : 0 ≤ 2/(scheduleCount e : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hnupper hd
  have hcancelN : (scheduleCount e : ℝ)*(2/(scheduleCount e : ℝ)) = 2 :=
    mul_div_cancel₀ _ hn.ne'
  have hcancelNe := congrArg (fun x : ℝ => x*e^2) hcancelN
  have hsprod := mul_le_mul_of_nonneg_right hu hs.le
  nlinarith only [hprod, hcancelNe, hsprod]

/-- The linear-in-inverse-tilt count gives an explicit quadratic saving. -/
theorem effective_count {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/10)
    (N : ℕ) (hN : 0 < N) (hcount : ⌈480/e⌉₊ ≤ N) :
    partitionCost (uniformPartition N hN) e ≤ 1/2-e^2/240 := by
  have hc : 480/e ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hcount)
  have hn : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hmul := (div_le_iff₀ he).mp hc
  have herr : 2*e/(N : ℝ) ≤ e^2/240 := by
    apply (div_le_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_right hmul he.le
    nlinarith only [hh]
  have hf := uniform_error N hN he.le he1
  have hj := J_quadratic_saving he.le he1
  have hf' := (abs_le.mp hf).2
  linarith only [herr, hj, hf']

/-- The source count schedule with explicit cubic and quartic terms. -/
theorem schedule_upper {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/10)
    (N : ℕ) (hN : 0 < N) (hcount : scheduleCount e ≤ N) :
    partitionCost (uniformPartition N hN) e ≤
      1/2-e^2/60+e^3/2+(9/2 : ℝ)*e^4 := by
  have hw := width_le_square he hN hcount
  exact (uniform_cost_upper N hN he.le he1).trans
    (continuum_plus_finiteBudget he.le he1 (by positivity) hw)

/-- Strict saving for the full proved range, including its upper endpoint. -/
theorem schedule_saving {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/50)
    (N : ℕ) (hN : 0 < N) (hcount : scheduleCount e ≤ N) :
    partitionCost (uniformPartition N hN) e ≤ 1/2-(73/15000 : ℝ)*e^2 ∧
    partitionCost (uniformPartition N hN) e < 1/2 := by
  have hbound := schedule_upper he (by linarith) N hN hcount
  have he2 : e^2 ≤ 1/2500 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/50-e by linarith) (show 0 ≤ 1/50+e by linarith)]
  have he3 := mul_le_mul_of_nonneg_right he1 (sq_nonneg e)
  have he4 := mul_le_mul_of_nonneg_right he2 (sq_nonneg e)
  have hsave : partitionCost (uniformPartition N hN) e ≤ 1/2-(73/15000 : ℝ)*e^2 := by
    nlinarith only [hbound, he3, he4]
  exact ⟨hsave, lt_of_le_of_lt hsave (by nlinarith [sq_pos_of_pos he])⟩

/-- Explicit two-sided remainder implies the claimed O(e^4) asymptotic.
The cubic coefficient is a property of the actual finite schedule. -/
theorem schedule_asymptotic {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/10) :
    |partitionCost (uniformPartition (scheduleCount e) (scheduleCount_pos he)) e -
      (1/2-e^2/60+e^3/2)| ≤ (9/2 : ℝ)*e^4 := by
  let d : ℝ := 2/(scheduleCount e : ℝ)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ e^2 := width_le_square he (scheduleCount_pos he) (le_refl _)
  have hd2 : e^2-e^4/2 ≤ d := schedule_width_lower he
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he.le he1
  have hf := uniform_cost_lower (scheduleCount e) (scheduleCount_pos he) he.le he1
  have hj := J_lower he.le he1
  have hm := (Mstar_small_bounds he.le he1).2.2.1.le
  have hdelta := uniformPadding_ge_half he.le (by linarith : e < 1) hd0
  have hweight : 0 ≤ 1-3*e^2/2 := by linarith
  have hpad := mul_le_mul_of_nonneg_right hdelta hweight
  have hmid : (3/8 : ℝ)*(Mstar e)^2*e^2*d ≤ (2/5 : ℝ)*e^4 := by
    have hh := mul_le_mul_of_nonneg_right hm (mul_nonneg (sq_nonneg e) hd0)
    have hh2 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg e)
    nlinarith only [hh, hh2, pow_nonneg he.le 4]
  have hpadlower : e^3/2-e^4/10 ≤ uniformPadding e d*(1-3*e^2/2) := by
    have hdlo := mul_le_mul_of_nonneg_right hd2 he.le
    have hdhi := mul_le_mul_of_nonneg_right hd1 (pow_nonneg he.le 3)
    have he5 := mul_le_mul_of_nonneg_right he1 (pow_nonneg he.le 4)
    nlinarith only [hpad, hdlo, hdhi, he5]
  have hlower : -(9/2 : ℝ)*e^4 ≤
      partitionCost (uniformPartition (scheduleCount e) (scheduleCount_pos he)) e -
        (1/2-e^2/60+e^3/2) := by
    change J e-(3/8 : ℝ)*(Mstar e)^2*e^2*d+uniformPadding e d*(1-3*e^2/2) ≤ _ at hf
    nlinarith only [hf, hj, hmid, hpadlower, pow_nonneg he.le 4]
  have hupper := schedule_upper he he1 (scheduleCount e) (scheduleCount_pos he) (le_refl _)
  exact abs_le.mpr ⟨by simpa only [neg_mul] using hlower,
    by linarith only [hupper]⟩

end
end TetrahedronCover
