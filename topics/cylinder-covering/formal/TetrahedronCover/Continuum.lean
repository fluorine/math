module

public import TetrahedronCover.Estimates
public import TetrahedronCover.Partition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FunProp

/-!
# The continuum integral and its rational remainder

The pointwise bounds are imported from Estimates. The exact coefficient
929/1260 is derived by polynomial integration and the fundamental theorem
of calculus.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section
open MeasureTheory intervalIntegral

/-- The limiting normalized area of the quartic cap. -/
def J (e : ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∫ q in (-1 : ℝ)..1, (C e q)^2 / Real.sqrt (1 + e^2 * D₀ q)

/-- The elementary polynomial integral, derived directly from the FTC. -/
theorem integral_nat_pow (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, x^n) = (b^(n+1)-a^(n+1))/(n+1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y^(n+1)/((n : ℝ)+1)) (x^n) x := by
    intro x _
    convert (hasDerivAt_pow (n+1) x).div_const ((n : ℝ)+1) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.pow n).intervalIntegrable a b)
  simpa only [← sub_div] using hi

theorem quadraticDensity_integral (e : ℝ) :
    (1/4 : ℝ) * ∫ q in (-1 : ℝ)..1, quadraticDensity e q =
      1/2-e^2/60+(929/1260 : ℝ)*e^4 := by
  simp_rw [quadraticDensity_eq]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_nat_pow]
  norm_num
  ring

theorem continuum_integrand_continuous (e : ℝ) :
    Continuous (fun q : ℝ => (C e q)^2 / Real.sqrt (1+e^2*D₀ q)) := by
  have hd : ∀ q : ℝ, 0 ≤ D₀ q := by
    intro q
    unfold D₀
    positivity
  apply Continuous.div
  · unfold C h G
    fun_prop
  · unfold D₀ G
    fun_prop
  · intro q
    exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [mul_nonneg (sq_nonneg e) (hd q)]))

/-- The exact quartic coefficient and explicit uniform sixth-order remainder. -/
theorem J_upper {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    J e ≤ 1/2-e^2/60+(929/1260 : ℝ)*e^4+4*e^6 := by
  have hf : IntervalIntegrable (fun q : ℝ => (C e q)^2 / Real.sqrt (1+e^2*D₀ q))
      volume (-1) 1 := (continuum_integrand_continuous e).intervalIntegrable (-1) 1
  have hpoly : Continuous (fun q : ℝ => quadraticDensity e q) := by
    unfold quadraticDensity h D₀ G
    fun_prop
  have hg : IntervalIntegrable (fun q : ℝ => quadraticDensity e q+8*e^6)
      volume (-1) 1 := (hpoly.add continuous_const).intervalIntegrable (-1) 1
  have hle := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    hf hg (fun q hq => continuum_integrand_upper he0 he1 hq)
  have hmajor : (1/4 : ℝ) *
      (∫ q in (-1 : ℝ)..1, quadraticDensity e q + 8*e^6) =
      1/2-e^2/60+(929/1260 : ℝ)*e^4+4*e^6 := by
    rw [intervalIntegral.integral_add (hpoly.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    have hi := quadraticDensity_integral e
    norm_num at *
    linarith
  unfold J
  rw [← hmajor]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

/-- A convenient strict quadratic saving, uniform through e = 1/10. -/
theorem J_quadratic_saving {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    J e ≤ 1/2-e^2/120 := by
  have he2 : e^2 ≤ 1/100 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/10-e by linarith)
      (show 0 ≤ 1/10+e by linarith)]
  have he4 : e^4 ≤ (1/100 : ℝ)*e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right he2 (sq_nonneg e)]
  have he6 : e^6 ≤ (1/10000 : ℝ)*e^2 := by
    have hstep := mul_le_mul_of_nonneg_right he4 (sq_nonneg e)
    nlinarith only [hstep, he4]
  have hj := J_upper he0 he1
  nlinarith only [hj, he4, he6, sq_nonneg e]
/-- All constants in the source count schedule, before the geometric sum bridge. -/
theorem continuum_plus_finiteBudget {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ e^2) :
    J e+finiteErrorBudget e d ≤ 1/2-e^2/60+e^3/2+(9/2 : ℝ)*e^4 := by
  have hj := J_upper he0 he1
  have hb := finiteErrorBudget_fine he0 he1 hd0 hd2
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he0 he1
  have he6 := mul_le_mul_of_nonneg_right he2 (pow_nonneg he0 4)
  nlinarith only [hj, hb, he6, pow_nonneg he0 4]

theorem C_continuous (e : ℝ) : Continuous (C e) := by
  unfold C h G
  fun_prop

theorem midpointWeight_continuous (e : ℝ) : Continuous (midpointWeight e) := by
  unfold midpointWeight
  apply Continuous.div continuous_const
  · unfold D₀ G
    fun_prop
  · intro q
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold D₀
    positivity

theorem inv_sqrt_bounds {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ 1/Real.sqrt (1+z) ∧ 1/Real.sqrt (1+z) ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1+z) := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+z by linarith)
    simpa using hh
  constructor
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1+z))).2
    simpa using hs

theorem midpointWeight_bounds (e q : ℝ) :
    0 ≤ midpointWeight e q ∧ midpointWeight e q ≤ 1 := by
  apply inv_sqrt_bounds
  unfold D₀
  positivity

theorem Cell.secantWeight_nonneg_le_one (I : Cell) (e : ℝ) :
    0 ≤ I.secantWeight e ∧ I.secantWeight e ≤ 1 := by
  apply inv_sqrt_bounds
  positivity

/-- The exact first absolute moment of a cell about its midpoint. -/
theorem Cell.integral_abs_mid (I : Cell) :
    (∫ q in I.left..I.right, |q-I.mid|) = I.width^2/4 := by
  have hlm := I.mid_mem.1
  have hmr := I.mid_mem.2
  have hc : Continuous (fun q : ℝ => |q-I.mid|) := by fun_prop
  have hleft : (∫ q in I.left..I.mid, |q-I.mid|) =
      ∫ q in I.left..I.mid, I.mid-q := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hlm] at hq
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hq.2)]
    ring
  have hright : (∫ q in I.mid..I.right, |q-I.mid|) =
      ∫ q in I.mid..I.right, q-I.mid := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hmr] at hq
    exact abs_of_nonneg (sub_nonneg.mpr hq.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable I.left I.mid) (hc.intervalIntegrable I.mid I.right), hleft, hright]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => I.mid) (g := fun q : ℝ => q)
      intervalIntegrable_const
      (continuous_id.intervalIntegrable I.left I.mid),
    intervalIntegral.integral_sub (f := fun q : ℝ => q) (g := fun _ : ℝ => I.mid)
      (continuous_id.intervalIntegrable I.mid I.right)
      intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hpow (a b : ℝ) : (∫ q in a..b, q) = (b^2-a^2)/2 := by
    have hh := integral_nat_pow 1 a b
    norm_num at hh
    exact hh
  rw [hpow, hpow]
  simp only [smul_eq_mul, Cell.mid, Cell.width]
  ring

theorem linearDensity_integral (e : ℝ) :
    (1/4:ℝ)*(∫ q in (-1:ℝ)..1, 1+e^2*(2*h q-D₀ q/2)) = 1/2-e^2/60 := by
  have hid (q : ℝ) : 1+e^2*(2*h q-D₀ q/2) = 1+(e^2/8)*(-1-2*q^2+7*q^4) := by
    unfold h D₀ G
    ring
  simp_rw [hid]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_nat_pow]
  norm_num
  ring

theorem J_lower {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    1/2-e^2/60-(3/2:ℝ)*e^4 ≤ J e := by
  have hp : Continuous (fun q : ℝ => 1+e^2*(2*h q-D₀ q/2)) := by
    unfold h D₀ G
    fun_prop
  have hl : IntervalIntegrable (fun q : ℝ => 1+e^2*(2*h q-D₀ q/2)-3*e^4)
      volume (-1) 1 := (hp.sub continuous_const).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun q : ℝ => (C e q)^2/Real.sqrt (1+e^2*D₀ q))
      volume (-1) 1 := (continuum_integrand_continuous e).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (-1:ℝ) ≤ 1) hl hr
    (fun q hq => continuum_integrand_lower he0 he1 hq)
  have hi := linearDensity_integral e
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at hm
  unfold J
  norm_num at hm
  linarith

theorem Cell.integrand_error_upper (I : Cell) {e q : ℝ}
    (he0 : 0 ≤ e) (he1 : e < 1) (hq : I.Mem q) :
    (I.cap e)^2*I.secantWeight e-(C e q)^2*midpointWeight e q ≤
      (2*Mstar e*I.padding e+(I.padding e)^2) + (Mstar e)^2*e^2*I.width^2/8 +
      3*(Mstar e)^2*e^2*|q-I.mid| +
      2*Mstar e*e^2*(capVariation I.right-capVariation I.left) := by
  let H := max (C e I.left) (C e I.right)
  have hCH : C e q ≤ H := I.C_le_endpoint_max hq
  have hC0 := (C_pos e q).le
  have hH0 : 0 ≤ H := hC0.trans hCH
  have hHM : H ≤ Mstar e := max_le (C_le_Mstar e I.left_abs_le)
    (C_le_Mstar e I.right_abs_le)
  have hH2 : H^2 ≤ (Mstar e)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHM) (show 0 ≤ Mstar e+H by linarith)]
  have hd := I.padding_nonneg he0 he1
  obtain ⟨hgs0, hgs1⟩ := I.secantWeight_nonneg_le_one e
  obtain ⟨hg0, hg1⟩ := midpointWeight_bounds e q
  obtain ⟨hsec0, hsec1⟩ := I.secantWeight_bounds e
  have hpad0 : 0 ≤ (I.cap e)^2-H^2 := by
    change 0 ≤ (H+I.padding e)^2-H^2
    nlinarith [mul_nonneg hH0 hd, sq_nonneg (I.padding e)]
  have hpad1 : (I.cap e)^2-H^2 ≤ 2*Mstar e*I.padding e+(I.padding e)^2 := by
    change (H+I.padding e)^2-H^2 ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right hHM hd]
  have hA : ((I.cap e)^2-H^2)*I.secantWeight e ≤
      2*Mstar e*I.padding e+(I.padding e)^2 := by
    have hh := mul_le_mul_of_nonneg_left hgs1 hpad0
    nlinarith only [hh, hpad1]
  have hB : H^2*(I.secantWeight e-midpointWeight e I.mid) ≤
      (Mstar e)^2*e^2*I.width^2/8 := by
    have hh := mul_le_mul hH2 hsec1 hsec0 (sq_nonneg (Mstar e))
    nlinarith only [hh]
  have hw := midpointWeight_lipschitz e I.mid_abs_le (I.mem_abs_le hq)
  have hC : H^2*(midpointWeight e I.mid-midpointWeight e q) ≤
      3*(Mstar e)^2*e^2*|q-I.mid| := by
    have ha := mul_le_mul_of_nonneg_left
      (neg_le_abs (midpointWeight e q-midpointWeight e I.mid)) (sq_nonneg H)
    have hb := mul_le_mul hH2 hw (abs_nonneg _) (sq_nonneg (Mstar e))
    nlinarith only [ha, hb]
  have hgap0 : 0 ≤ H-C e q := sub_nonneg.mpr hCH
  have hgap2 : 0 ≤ H^2-(C e q)^2 := by
    nlinarith [mul_nonneg hgap0 (show 0 ≤ H+C e q by linarith)]
  have hsum : H+C e q ≤ 2*Mstar e := by linarith
  have hsq := mul_le_mul_of_nonneg_right hsum hgap0
  have hvar := I.maximum_cap_error e hq
  have hvar' := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 2*Mstar e by linarith)
  have hD : (H^2-(C e q)^2)*midpointWeight e q ≤
      2*Mstar e*e^2*(capVariation I.right-capVariation I.left) := by
    have hh := mul_le_mul_of_nonneg_left hg1 hgap2
    change H-C e q ≤ _ at hvar
    change 2*Mstar e*(H-C e q) ≤ _ at hvar'
    nlinarith only [hh, hsq, hvar']
  nlinarith only [hA, hB, hC, hD]

theorem Cell.integrand_error_lower (I : Cell) {e q : ℝ}
    (he0 : 0 ≤ e) (he1 : e < 1) (hq : I.Mem q) :
    (C e q)^2*midpointWeight e q-(I.cap e)^2*I.secantWeight e ≤
      3*(Mstar e)^2*e^2*|q-I.mid|-2*I.padding e*(1-3*e^2/2) := by
  have hC1 := C_ge_one e q
  have hC0 := (C_pos e q).le
  have hCM := C_le_Mstar e (I.mem_abs_le hq)
  have hC2 : (C e q)^2 ≤ (Mstar e)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCM)
      (show 0 ≤ Mstar e+C e q by linarith)]
  have hd := I.padding_nonneg he0 he1
  have hc := I.cap_ge hq (e := e)
  have hcp0 : 0 ≤ I.cap e := by linarith
  have hc2 : (C e q)^2+2*I.padding e ≤ (I.cap e)^2 := by
    have ha := mul_le_mul hc hc (show 0 ≤ C e q+I.padding e by positivity) hcp0
    have hb := mul_nonneg (show 0 ≤ C e q-1 by linarith) hd
    nlinarith [sq_nonneg (I.padding e)]
  have hgc0 := (midpointWeight_bounds e I.mid).1
  have hsec0 := (I.secantWeight_bounds e).1
  have ha := mul_le_mul_of_nonneg_right hc2 hgc0
  have hb := mul_le_mul_of_nonneg_left (show midpointWeight e I.mid ≤ I.secantWeight e by linarith)
    (sq_nonneg (I.cap e))
  have hD := D₀_bounds (show I.mid ∈ Set.Icc (-1:ℝ) 1 from abs_le.mp I.mid_abs_le)
  have hlin := linear_le_inv_sqrt (mul_nonneg (sq_nonneg e) hD.1)
  have hDb := mul_le_mul_of_nonneg_left hD.2 (sq_nonneg e)
  have hgc : 1-3*e^2/2 ≤ midpointWeight e I.mid := by
    unfold midpointWeight
    nlinarith only [hlin, hDb]
  have hp := mul_le_mul_of_nonneg_left hgc (show 0 ≤ 2*I.padding e by positivity)
  have hw := midpointWeight_lipschitz e I.mid_abs_le (I.mem_abs_le hq)
  have hmid1 := mul_le_mul_of_nonneg_left
    (le_abs_self (midpointWeight e q-midpointWeight e I.mid)) (sq_nonneg (C e q))
  have hmid2 := mul_le_mul hC2 hw (abs_nonneg _) (sq_nonneg (Mstar e))
  nlinarith only [ha, hb, hp, hmid1, hmid2]

def Cell.integralCost (I : Cell) (e : ℝ) : ℝ :=
  (1/4:ℝ)*∫ q in I.left..I.right, (C e q)^2*midpointWeight e q

theorem density_continuous (e : ℝ) :
    Continuous (fun q : ℝ => (C e q)^2*midpointWeight e q) :=
  (C_continuous e).pow 2 |>.mul (midpointWeight_continuous e)

theorem Cell.term_weight_identity (I : Cell) (e : ℝ) :
    4*I.term e = I.width*(I.cap e)^2*I.secantWeight e := by
  unfold Cell.term Cell.secantWeight
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The full upper finite error, integrated on one arbitrary cell. -/
theorem Cell.integrated_error_upper (I : Cell) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    I.term e-I.integralCost e ≤
      I.width*(2*Mstar e*I.padding e+(I.padding e)^2)/4 +
      (Mstar e)^2*e^2*I.width^3/32 + 3*(Mstar e)^2*e^2*I.width^2/16 +
      Mstar e*e^2*I.width*(capVariation I.right-capVariation I.left)/2 := by
  let B := (2*Mstar e*I.padding e+(I.padding e)^2) +
    (Mstar e)^2*e^2*I.width^2/8 +
    2*Mstar e*e^2*(capVariation I.right-capVariation I.left)
  have hl : IntervalIntegrable
      (fun q : ℝ => (I.cap e)^2*I.secantWeight e-(C e q)^2*midpointWeight e q)
      volume I.left I.right :=
    (continuous_const.sub (density_continuous e)).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun q : ℝ => B+3*(Mstar e)^2*e^2*|q-I.mid|)
      volume I.left I.right := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on I.strict.le hl hr (fun q hq => by
    have hh := I.integrand_error_upper he0 he1 hq
    dsimp [B]
    linarith only [hh])
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (I.cap e)^2*I.secantWeight e)
      (g := fun q : ℝ => (C e q)^2*midpointWeight e q) intervalIntegrable_const
      ((density_continuous e).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun _ : ℝ => B)
      (g := fun q : ℝ => 3*(Mstar e)^2*e^2*|q-I.mid|) intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, I.integral_abs_mid] at hm
  simp only [smul_eq_mul] at hm
  have ht := I.term_weight_identity e
  unfold Cell.integralCost
  dsimp [B, Cell.width] at hm ht ⊢
  nlinarith only [hm, ht]

/-- The lower finite error retains the leading linear padding contribution. -/
theorem Cell.integrated_error_lower (I : Cell) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    I.integralCost e-3*(Mstar e)^2*e^2*I.width^2/16 +
      I.width*I.padding e*(1-3*e^2/2)/2 ≤ I.term e := by
  have hl : IntervalIntegrable
      (fun q : ℝ => (C e q)^2*midpointWeight e q-(I.cap e)^2*I.secantWeight e)
      volume I.left I.right :=
    ((density_continuous e).sub continuous_const).intervalIntegrable _ _
  have hr : IntervalIntegrable
      (fun q : ℝ => 3*(Mstar e)^2*e^2*|q-I.mid|-2*I.padding e*(1-3*e^2/2))
      volume I.left I.right := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on I.strict.le hl hr
    (fun q hq => I.integrand_error_lower he0 he1 hq)
  rw [intervalIntegral.integral_sub (f := fun q : ℝ => (C e q)^2*midpointWeight e q)
      (g := fun _ : ℝ => (I.cap e)^2*I.secantWeight e)
      ((density_continuous e).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_sub (f := fun q : ℝ => 3*(Mstar e)^2*e^2*|q-I.mid|)
      (g := fun _ : ℝ => 2*I.padding e*(1-3*e^2/2))
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, I.integral_abs_mid] at hm
  simp only [smul_eq_mul] at hm
  have ht := I.term_weight_identity e
  unfold Cell.integralCost
  dsimp [Cell.width] at hm ht ⊢
  nlinarith only [hm, ht]

/-- Exact normalized area of the finite family, with labelled multiplicity. -/
def partitionCost (P : Partition) (e : ℝ) : ℝ := ∑ i, (P.cell i).term e

theorem Partition.sum_integralCost (P : Partition) (e : ℝ) :
    (∑ i, (P.cell i).integralCost e) = J e := by
  simp only [Cell.integralCost, ← Finset.mul_sum]
  change (1/4:ℝ)*(∑ i : Fin P.count,
    ∫ q in P.node i..P.node (i+1), (C e q)^2*midpointWeight e q) = J e
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ q in P.node i..P.node (i+1), (C e q)^2*midpointWeight e q) P.count]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => (density_continuous e).intervalIntegrable (P.node k) (P.node (k+1)))]
  rw [P.first, P.last]
  unfold J
  congr 1
  apply intervalIntegral.integral_congr
  intro q _
  simp only [midpointWeight, div_eq_mul_inv, one_mul]

theorem Partition.sum_capVariation (P : Partition) :
    (∑ i : Fin P.count, (capVariation (P.cell i).right - capVariation (P.cell i).left)) = 2 := by
  change (∑ i : Fin P.count,
    (capVariation (P.node (i+1)) - capVariation (P.node i))) = 2
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      capVariation (P.node (i+1))-capVariation (P.node i)) P.count,
    Finset.sum_range_sub (fun i : ℕ => capVariation (P.node i)) P.count, P.first, P.last]
  exact capVariation_endpoints

theorem uniform_cost_upper (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    partitionCost (uniformPartition N hN) e ≤ J e+finiteErrorBudget e (2/(N:ℝ)) := by
  let P := uniformPartition N hN
  let d : ℝ := 2/(N:ℝ)
  let δ := uniformPadding e d
  let U := d*(2*Mstar e*δ+δ^2)/4 + (Mstar e)^2*e^2*d^3/32 +
    3*(Mstar e)^2*e^2*d^2/16
  let V := Mstar e*e^2*d/2
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hNd : (N:ℝ)*d = 2 := by dsimp [d]; field_simp
  have hcell (i : Fin N) : (P.cell i).term e-(P.cell i).integralCost e ≤
      U+V*(capVariation (P.cell i).right-capVariation (P.cell i).left) := by
    have hh := (P.cell i).integrated_error_upper he0 (by linarith : e < 1)
    dsimp only [P] at hh
    simp only [Cell.padding_eq_uniform, uniformPartition_width] at hh
    convert hh using 1
    dsimp [U, V, δ, d, P]
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hcell i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hv := P.sum_capVariation
  rw [Finset.sum_sub_distrib] at hv
  rw [P.sum_integralCost e, hv] at hs
  have hid : (N:ℝ)*U+V*2 = finiteErrorBudget e d := by
    calc
      (N:ℝ)*U+V*2 = (N*d)*((2*Mstar e*δ+δ^2)/4 +
          (Mstar e)^2*e^2*d^2/32+3*(Mstar e)^2*e^2*d/16)+V*2 := by
        dsimp [U]
        ring
      _ = finiteErrorBudget e d := by
        rw [hNd]
        dsimp [finiteErrorBudget, V, δ]
        ring
  rw [hid] at hs
  change (∑ i, (P.cell i).term e)-J e ≤ finiteErrorBudget e d at hs
  change (∑ i, (P.cell i).term e) ≤ J e+finiteErrorBudget e d
  linarith only [hs]

theorem uniform_cost_lower (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    J e-(3/8:ℝ)*(Mstar e)^2*e^2*(2/(N:ℝ)) +
      uniformPadding e (2/(N:ℝ))*(1-3*e^2/2) ≤ partitionCost (uniformPartition N hN) e := by
  let P := uniformPartition N hN
  let d : ℝ := 2/(N:ℝ)
  let δ := uniformPadding e d
  let L := -3*(Mstar e)^2*e^2*d^2/16+d*δ*(1-3*e^2/2)/2
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hNd : (N:ℝ)*d = 2 := by dsimp [d]; field_simp
  have hcell (i : Fin N) : (P.cell i).integralCost e+L ≤ (P.cell i).term e := by
    have hh := (P.cell i).integrated_error_lower he0 (by linarith : e < 1)
    dsimp only [P] at hh
    simp only [Cell.padding_eq_uniform, uniformPartition_width] at hh
    convert hh using 1
    dsimp [L, δ, d, P]
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hcell i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  rw [P.sum_integralCost e] at hs
  have hid : (N:ℝ)*L = -(3/8:ℝ)*(Mstar e)^2*e^2*d+δ*(1-3*e^2/2) := by
    calc
      (N:ℝ)*L = (N*d)*(-3*(Mstar e)^2*e^2*d/16+δ*(1-3*e^2/2)/2) := by
        dsimp [L]
        ring
      _ = _ := by rw [hNd]; ring
  rw [hid] at hs
  change _ ≤ ∑ i, (P.cell i).term e
  dsimp [δ, d] at hs
  linarith only [hs]

theorem uniform_error (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    |partitionCost (uniformPartition N hN) e-J e| ≤ 2*e/(N:ℝ) := by
  let d : ℝ := 2/(N:ℝ)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd2 : d ≤ 2 := by
    dsimp [d]
    apply (div_le_iff₀ hN0).2
    linarith
  have hup := uniform_cost_upper N hN he0 he1
  have hlo := uniform_cost_lower N hN he0 he1
  have hbudget := finiteErrorBudget_le he0 he1 hd0 hd2
  have hpad0 := uniformPadding_nonneg he0 (by linarith) hd0
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he0 he1
  have hpad : 0 ≤ uniformPadding e d*(1-3*e^2/2) :=
    mul_nonneg hpad0 (by linarith)
  obtain ⟨_, _, hm2, _⟩ := Mstar_small_bounds he0 he1
  have hMe : (Mstar e)^2*e ≤ (1023/1000:ℝ)*(1/10) :=
    mul_le_mul hm2.le he1 he0 (by norm_num)
  have hloss := mul_le_mul_of_nonneg_right hMe (mul_nonneg he0 hd0)
  have heD := mul_nonneg he0 hd0
  have heq : 2*e/(N:ℝ) = e*d := by dsimp [d]; ring
  rw [heq, abs_le]
  change _ ≤ J e+finiteErrorBudget e d at hup
  change J e-(3/8:ℝ)*(Mstar e)^2*e^2*d+uniformPadding e d*(1-3*e^2/2) ≤ _ at hlo
  constructor <;> nlinarith only [hup, hlo, hbudget, hpad, hloss, heD]


end
end TetrahedronCover
