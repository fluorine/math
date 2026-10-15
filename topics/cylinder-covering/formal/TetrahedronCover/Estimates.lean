module

public import TetrahedronCover.Algebra
public import Mathlib.Tactic.FieldSimp

/-!
# Algebraic majorants and finite-area constants

These statements estimate the explicit functions themselves. The reciprocal
square-root majorant is proved by exact factorization; no calculus estimate
or finite-area bound is assumed.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section

/-- The terms of degree at most four in the continuum integrand. -/
def quadraticDensity (e q : ℝ) : ℝ :=
  1 + e^2 * (2*h q - D₀ q/2) +
    e^4 * ((h q)^2 + (9/8 : ℝ) - h q*D₀ q + (3/8 : ℝ)*(D₀ q)^2)

/-- An algebraic proof of the quadratic reciprocal-square-root majorant. -/
theorem inv_sqrt_le_quadratic {z : ℝ} (hz : 0 ≤ z) :
    1 / Real.sqrt (1+z) ≤ 1 - z/2 + (3/8 : ℝ)*z^2 := by
  let s := Real.sqrt (1+z)
  have hs : 1 ≤ s := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1+z by linarith)
    simpa [s] using hh
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsq : s^2 = 1+z := Real.sq_sqrt (by linarith)
  have hm : 0 ≤ s-1 := by linarith
  have hp : 0 ≤ 3*s^2+9*s+8 := by positivity
  have hfactor : s*(1-z/2+(3/8 : ℝ)*z^2)-1 =
      (s-1)^3*(3*s^2+9*s+8)/8 := by
    rw [show z = s^2-1 by linarith]
    ring
  have hnonneg : 0 ≤ (s-1)^3*(3*s^2+9*s+8)/8 :=
    div_nonneg (mul_nonneg (pow_nonneg hm _) hp) (by norm_num)
  change 1 / s ≤ _
  apply (div_le_iff₀ hspos).2
  nlinarith only [hfactor, hnonneg]

theorem h_bounds {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ h q ∧ h q ≤ 1 := by
  have hq0 := sq_nonneg q
  have hq1 : q^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-q by linarith [hq.2])
      (show 0 ≤ 1+q by linarith [hq.1])]
  have hG0 : 0 ≤ G q := by unfold G; positivity
  have hG1 : G q ≤ 1 := by unfold G; linarith
  constructor
  · exact mul_nonneg hq0 hG0
  · unfold h
    exact (mul_le_mul_of_nonneg_left hG1 hq0).trans (by simpa using hq1)

theorem D₀_bounds {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ D₀ q ∧ D₀ q ≤ 3 := by
  have hq0 := sq_nonneg q
  have hq1 : q^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-q by linarith [hq.2])
      (show 0 ≤ 1+q by linarith [hq.1])]
  have hG0 : 0 ≤ G q := by unfold G; positivity
  have hG1 : G q ≤ 1 := by unfold G; linarith
  have hG2 : (G q)^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-G q by linarith)
      (show 0 ≤ 1+G q by linarith)]
  unfold D₀
  constructor
  · positivity
  · linarith

private theorem remainder_coefficients {H T : ℝ}
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hT0 : 0 ≤ T) (hT3 : T ≤ 3) :
    (3/4 : ℝ)*H*T^2 - T*(H^2+9/8)/2 + (9/8 : ℝ)*H ≤ 63/8 ∧
    (3/8 : ℝ)*T^2*(H^2+9/8) - (9/16 : ℝ)*T*H + 81/256 ≤ 1917/256 ∧
    (27/64 : ℝ)*H*T^2 - (81/512 : ℝ)*T ≤ 243/64 ∧
    (243/2048 : ℝ)*T^2 ≤ 2187/2048 := by
  have hH2 : H^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-H by linarith)
      (show 0 ≤ 1+H by linarith)]
  have hT2 : T^2 ≤ 9 := by
    nlinarith [mul_nonneg (show 0 ≤ 3-T by linarith)
      (show 0 ≤ 3+T by linarith)]
  have hHT : H*T^2 ≤ 9 := by
    calc
      H*T^2 ≤ 1*T^2 := mul_le_mul_of_nonneg_right hH1 (sq_nonneg T)
      _ ≤ 9 := by simpa using hT2
  have hTT : T^2*(H^2+9/8) ≤ 9*(1+9/8 : ℝ) := by
    exact mul_le_mul hT2 (by linarith) (by positivity) (by norm_num)
  have hn3 : 0 ≤ T*(H^2+9/8) := mul_nonneg hT0 (by positivity)
  have hn4 : 0 ≤ T*H := mul_nonneg hT0 hH0
  constructor
  · nlinarith only [hHT, hn3, hH1]
  constructor
  · nlinarith only [hTT, hn4]
  constructor
  · nlinarith only [hHT, hT0]
  · linarith

private theorem polynomial_majorant {u H T : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/100)
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hT0 : 0 ≤ T) (hT3 : T ≤ 3) :
    (1+u*H+(9/16 : ℝ)*u^2)^2 * (1-u*T/2+(3/8 : ℝ)*(u*T)^2) ≤
      1+u*(2*H-T/2)+u^2*(H^2+9/8-H*T+(3/8 : ℝ)*T^2)+8*u^3 := by
  obtain ⟨hc3, hc4, hc5, hc6⟩ := remainder_coefficients hH0 hH1 hT0 hT3
  have hu2 : u^2 ≤ (1/100 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/100-u by linarith)
      (show 0 ≤ 1/100+u by linarith)]
  have hu3 : u^3 ≤ (1/100 : ℝ)^3 := by
    calc
      u^3 = u^2*u := by ring
      _ ≤ (1/100 : ℝ)^2*(1/100 : ℝ) :=
        mul_le_mul hu2 hu1 hu0 (by positivity)
      _ = _ := by ring
  have hb : (63/8 : ℝ) + (1917/256 : ℝ)*u +
      (243/64 : ℝ)*u^2 + (2187/2048 : ℝ)*u^3 ≤ 8 := by
    nlinarith only [hu1, hu2, hu3]
  have h3 := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hu0 3)
  have h4 := mul_le_mul_of_nonneg_right hc4 (pow_nonneg hu0 4)
  have h5 := mul_le_mul_of_nonneg_right hc5 (pow_nonneg hu0 5)
  have h6 := mul_le_mul_of_nonneg_right hc6 (pow_nonneg hu0 6)
  have hb3 := mul_le_mul_of_nonneg_right hb (pow_nonneg hu0 3)
  nlinarith only [h3, h4, h5, h6, hb3]

theorem continuum_integrand_upper {e q : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) (hq : q ∈ Set.Icc (-1 : ℝ) 1) :
    (C e q)^2 / Real.sqrt (1+e^2*D₀ q) ≤ quadraticDensity e q + 8*e^6 := by
  obtain ⟨hh0, hh1⟩ := h_bounds hq
  obtain ⟨hd0, hd3⟩ := D₀_bounds hq
  have he2 : e^2 ≤ 1/100 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/10-e by linarith)
      (show 0 ≤ 1/10+e by linarith)]
  have hquad := mul_le_mul_of_nonneg_left
    (inv_sqrt_le_quadratic (mul_nonneg (sq_nonneg e) hd0)) (sq_nonneg (C e q))
  have hpoly := polynomial_majorant (sq_nonneg e) he2 hh0 hh1 hd0 hd3
  calc
    (C e q)^2 / Real.sqrt (1+e^2*D₀ q) ≤
        (C e q)^2*(1-e^2*D₀ q/2+(3/8 : ℝ)*(e^2*D₀ q)^2) := by
      simpa [div_eq_mul_inv] using hquad
    _ ≤ quadraticDensity e q + 8*e^6 := by
      convert hpoly using 1 <;> simp only [C, quadraticDensity] <;> ring

theorem quadraticDensity_eq (e q : ℝ) :
    quadraticDensity e q =
      1 + (e^2/8)*(-1-2*q^2+7*q^4) +
      (e^4/128)*(147+44*q^2+162*q^4-52*q^6+19*q^8) := by
  unfold quadraticDensity h D₀ G
  ring

def uniformPadding (e d : ℝ) : ℝ :=
  d * (Mstar e*(e+e^2/2)+2*e^2+Mstar e*e^2*d/4) / (2*(1-e))

theorem Cell.padding_eq_uniform (I : Cell) (e : ℝ) :
    I.padding e = uniformPadding e I.width := by
  simp only [Cell.padding, Cell.half, K₀, uniformPadding, div_eq_mul_inv, mul_inv_rev]
  ring

theorem uniformPadding_factor (e d : ℝ) :
    uniformPadding e d =
      (e*d)*(Mstar e*(1+e/2+e*d/4)+2*e)/(2*(1-e)) := by
  unfold uniformPadding
  congr 1
  ring

theorem small_parameter_powers {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    e^2 ≤ 1/100 ∧ e^2 ≤ e/10 ∧ e^4 ≤ 1/10000 ∧ e^4 ≤ e^2/100 := by
  have h2 : e^2 ≤ 1/100 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/10-e by linarith)
      (show 0 ≤ 1/10+e by linarith)]
  have h21 := mul_le_mul_of_nonneg_right he1 he0
  have h42 := mul_le_mul_of_nonneg_right h2 (sq_nonneg e)
  have h4 : e^4 ≤ 1/10000 := by
    nlinarith only [h2, h42]
  exact ⟨h2, by nlinarith only [h21], h4, by nlinarith only [h42]⟩

theorem Mstar_small_bounds {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    Mstar e ≤ 1+(81/80 : ℝ)*e^2 ∧ Mstar e < 1011/1000 ∧
    (Mstar e)^2 < 1023/1000 ∧ Mstar e+(3/8 : ℝ)*(Mstar e)^2 < 7/5 := by
  obtain ⟨h2, _, h4, h42⟩ := small_parameter_powers he0 he1
  have hm1 : Mstar e ≤ 1+(81/80 : ℝ)*e^2 := by
    unfold Mstar
    nlinarith only [h42, sq_nonneg e]
  have hm2 : Mstar e < 1011/1000 := by
    unfold Mstar
    nlinarith only [h2, h4]
  have hm0 := Mstar_ge_one e
  have hm3 : (Mstar e)^2 < 1023/1000 := by
    nlinarith [mul_pos (show 0 < 1011/1000-Mstar e by linarith)
      (show 0 < 1011/1000+Mstar e by linarith)]
  exact ⟨hm1, hm2, hm3, by linarith⟩

theorem uniformPadding_nonneg {e d : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hd0 : 0 ≤ d) : 0 ≤ uniformPadding e d := by
  unfold uniformPadding
  have hm := Mstar_pos e
  have hden : 0 < 2*(1-e) := by linarith
  positivity

theorem uniformPadding_coarse {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    uniformPadding e d ≤ (3/4 : ℝ)*e*d := by
  obtain ⟨_, hm, _, _⟩ := Mstar_small_bounds he0 he1
  have hed : e*d ≤ 1/5 := by
    calc
      e*d ≤ (1/10 : ℝ)*2 := mul_le_mul he1 hd2 hd0 (by norm_num)
      _ = _ := by norm_num
  have hfac0 : 0 ≤ 1+e/2+e*d/4 := by positivity
  have hfac1 : 1+e/2+e*d/4 ≤ 11/10 := by linarith
  have hQ : Mstar e*(1+e/2+e*d/4)+2*e ≤ 27/20 := by
    have hprod := mul_le_mul hm.le hfac1 hfac0 (by norm_num : (0:ℝ) ≤ 1011/1000)
    nlinarith only [hprod, he1]
  have hden : 0 < 2*(1-e) := by linarith
  rw [uniformPadding_factor, div_le_iff₀ hden]
  have hnum := mul_le_mul_of_nonneg_left hQ (mul_nonneg he0 hd0)
  have hdenbound : (27/20 : ℝ) ≤ (3/4 : ℝ)*(2*(1-e)) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hdenbound (mul_nonneg he0 hd0)
  nlinarith only [hnum, hscaled]

theorem uniformPadding_fine {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ e^2) :
    uniformPadding e d ≤ e*d/2+(21/10 : ℝ)*e^2*d := by
  obtain ⟨hm, _, _, _⟩ := Mstar_small_bounds he0 he1
  obtain ⟨he2, he21, _, _⟩ := small_parameter_powers he0 he1
  have he3 : e^3 ≤ e^2/10 := by
    nlinarith only [mul_le_mul_of_nonneg_right he1 (sq_nonneg e)]
  have he5 : e^5 ≤ e^2/1000 := by
    have hh := mul_le_mul_of_nonneg_right he2 (pow_nonneg he0 3)
    nlinarith only [hh, he3]
  have hfac0 : 0 ≤ 1+e/2+e*d/4 := by positivity
  have hfac1 : 1+e/2+e*d/4 ≤ 1+e/2+e^3/4 := by
    nlinarith only [mul_le_mul_of_nonneg_left hd2 he0]
  have hprod := mul_le_mul hm hfac1 hfac0 (by positivity : (0:ℝ) ≤ 1+(81/80 : ℝ)*e^2)
  have hQ : Mstar e*(1+e/2+e*d/4)+2*e ≤ 1+(5/2 : ℝ)*e+(11/10 : ℝ)*e^2 := by
    nlinarith only [hprod, he3, he5, sq_nonneg e]
  have hQden : Mstar e*(1+e/2+e*d/4)+2*e ≤ (1-e)*(1+(21/5 : ℝ)*e) := by
    nlinarith only [hQ, he21, he0]
  have hden : 0 < 2*(1-e) := by linarith
  rw [uniformPadding_factor, div_le_iff₀ hden]
  have hnum := mul_le_mul_of_nonneg_left hQden (mul_nonneg he0 hd0)
  nlinarith only [hnum]

theorem uniformPadding_fine_cubic {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ e^2) :
    uniformPadding e d ≤ (71/100 : ℝ)*e^3 := by
  have hp := uniformPadding_fine he0 he1 hd0 hd2
  have h1 := mul_le_mul_of_nonneg_left hd2 he0
  have h2 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg e)
  have h3 := mul_le_mul_of_nonneg_right he1 (pow_nonneg he0 3)
  nlinarith only [hp, h1, h2, h3]

/-- The four explicit upper discretization terms in equation (18). -/
def finiteErrorBudget (e d : ℝ) : ℝ :=
  (Mstar e+(3/8 : ℝ)*(Mstar e)^2)*e^2*d +
    Mstar e*uniformPadding e d + (uniformPadding e d)^2/2 +
    (Mstar e)^2*e^2*d^2/16

theorem finiteErrorBudget_le {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) : finiteErrorBudget e d ≤ e*d := by
  obtain ⟨_, hm1, hm2, hm3⟩ := Mstar_small_bounds he0 he1
  have hp := uniformPadding_coarse he0 he1 hd0 hd2
  have hp0 := uniformPadding_nonneg he0 (by linarith) hd0
  have hed0 : 0 ≤ e*d := mul_nonneg he0 hd0
  have hed1 : e*d ≤ 1/5 := by
    calc
      e*d ≤ (1/10 : ℝ)*2 := mul_le_mul he1 hd2 hd0 (by norm_num)
      _ = _ := by norm_num
  have hed2 : (e*d)^2 ≤ (1/5 : ℝ)*(e*d) := by
    nlinarith only [mul_le_mul_of_nonneg_right hed1 hed0]
  have hterm1 : (Mstar e+(3/8 : ℝ)*(Mstar e)^2)*e^2*d ≤ (7/50 : ℝ)*(e*d) := by
    have ha := mul_le_mul_of_nonneg_right hm3.le (mul_nonneg (sq_nonneg e) hd0)
    have hb := mul_le_mul_of_nonneg_right he1 hed0
    nlinarith only [ha, hb]
  have hterm2 : Mstar e*uniformPadding e d ≤ (3033/4000 : ℝ)*(e*d) := by
    have ha := mul_le_mul hm1.le hp hp0 (by norm_num : (0:ℝ) ≤ 1011/1000)
    nlinarith only [ha]
  have hterm3 : (uniformPadding e d)^2/2 ≤ (9/160 : ℝ)*(e*d) := by
    have ha := mul_le_mul hp hp hp0 (by positivity : (0:ℝ) ≤ (3/4 : ℝ)*e*d)
    nlinarith only [ha, hed2]
  have hterm4 : (Mstar e)^2*e^2*d^2/16 ≤ (1023/80000 : ℝ)*(e*d) := by
    have ha := mul_le_mul_of_nonneg_right hm2.le (sq_nonneg (e*d))
    nlinarith only [ha, hed2]
  unfold finiteErrorBudget
  nlinarith only [hterm1, hterm2, hterm3, hterm4, hed0]

theorem finiteErrorBudget_fine {e d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hd0 : 0 ≤ d) (hd2 : d ≤ e^2) :
    finiteErrorBudget e d ≤ e^3/2+(448/125 : ℝ)*e^4 := by
  obtain ⟨hm1, _, hm2, hm3⟩ := Mstar_small_bounds he0 he1
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he0 he1
  have hp := uniformPadding_fine he0 he1 hd0 hd2
  have hpc := uniformPadding_fine_cubic he0 he1 hd0 hd2
  have hp0 := uniformPadding_nonneg he0 (by linarith) hd0
  have he4 := pow_nonneg he0 4
  have he5 : e^5 ≤ e^4/10 := by
    nlinarith only [mul_le_mul_of_nonneg_right he1 he4]
  have he6 : e^6 ≤ e^4/100 := by
    nlinarith only [mul_le_mul_of_nonneg_right he2 he4]
  have hd4 : d^2 ≤ e^4 := by
    nlinarith only [mul_le_mul hd2 hd2 hd0 (sq_nonneg e)]
  have hterm1 : (Mstar e+(3/8 : ℝ)*(Mstar e)^2)*e^2*d ≤ (7/5 : ℝ)*e^4 := by
    have ha := mul_le_mul_of_nonneg_right hm3.le (mul_nonneg (sq_nonneg e) hd0)
    have hb := mul_le_mul_of_nonneg_left hd2 (sq_nonneg e)
    nlinarith only [ha, hb]
  have hterm2 : Mstar e*uniformPadding e d ≤ e^3/2+(109/50 : ℝ)*e^4 := by
    have hM : Mstar e-1 ≤ (81/80 : ℝ)*e^2 := by linarith
    have ha := mul_le_mul hM hpc hp0 (by positivity : (0:ℝ) ≤ (81/80 : ℝ)*e^2)
    have hb := mul_le_mul_of_nonneg_left hd2 he0
    have hc := mul_le_mul_of_nonneg_left hd2 (sq_nonneg e)
    nlinarith only [ha, hb, hc, hp, he5, he4]
  have hterm3 : (uniformPadding e d)^2/2 ≤ (3/1000 : ℝ)*e^4 := by
    have ha := mul_le_mul hpc hpc hp0 (by positivity : (0:ℝ) ≤ (71/100 : ℝ)*e^3)
    nlinarith only [ha, he6, he4]
  have hterm4 : (Mstar e)^2*e^2*d^2/16 ≤ (1/1000 : ℝ)*e^4 := by
    have ha := mul_le_mul_of_nonneg_right hm2.le (mul_nonneg (sq_nonneg e) (sq_nonneg d))
    have hb := mul_le_mul_of_nonneg_left hd4 (sq_nonneg e)
    nlinarith only [ha, hb, he6, he4]
  unfold finiteErrorBudget
  nlinarith only [hterm1, hterm2, hterm3, hterm4]

/-- An exact difference estimate for the inverse square root on the positive ray. -/
theorem inv_sqrt_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ 1/Real.sqrt (1+a)-1/Real.sqrt (1+b) ∧
    1/Real.sqrt (1+a)-1/Real.sqrt (1+b) ≤ (b-a)/2 := by
  let s := Real.sqrt (1+a)
  let t := Real.sqrt (1+b)
  have hs : 1 ≤ s := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+a by linarith)
    simpa [s] using hh
  have ht : 1 ≤ t := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+b by linarith)
    simpa [t] using hh
  have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hs2 : s^2 = 1+a := Real.sq_sqrt (by linarith)
  have ht2 : t^2 = 1+b := Real.sq_sqrt (by linarith)
  have hmul : 1 ≤ s*t := by
    nlinarith [mul_nonneg (show 0 ≤ s-1 by linarith) (show 0 ≤ t-1 by linarith)]
  have hprod : 2 ≤ (s+t)*(s*t) := by
    have hh := mul_le_mul (show (2:ℝ) ≤ s+t by linarith) hmul
      (by norm_num : (0:ℝ) ≤ 1) (show 0 ≤ s+t by linarith)
    nlinarith only [hh]
  have hid : 1/s-1/t = (t-s)/(s*t) := by
    field_simp
  change 0 ≤ 1/s-1/t ∧ 1/s-1/t ≤ (b-a)/2
  rw [hid]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hst) (mul_nonneg hs0.le ht0.le)
  · apply (div_le_iff₀ (mul_pos hs0 ht0)).2
    have hn := mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ (s+t)*(s*t)-2 by linarith)
    have hid' : (b-a)*(s*t)/2-(t-s) = (t-s)*((s+t)*(s*t)-2)/2 := by
      rw [show a = s^2-1 by linarith, show b = t^2-1 by linarith]
      ring
    nlinarith only [hn, hid']

theorem inv_sqrt_abs_difference {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |1/Real.sqrt (1+a)-1/Real.sqrt (1+b)| ≤ |a-b|/2 := by
  rcases le_total a b with hab | hba
  · obtain ⟨h0, h1⟩ := inv_sqrt_difference ha hab
    rw [abs_of_nonneg h0, abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith
  · obtain ⟨h0, h1⟩ := inv_sqrt_difference hb hba
    rw [abs_sub_comm (1/Real.sqrt (1+a)), abs_sub_comm a]
    rw [abs_of_nonneg h0, abs_of_nonpos (sub_nonpos.mpr hba)]
    linarith

def midpointWeight (e q : ℝ) : ℝ := 1/Real.sqrt (1+e^2*D₀ q)
def Cell.secantWeight (I : Cell) (e : ℝ) : ℝ :=
  1/Real.sqrt (1+e^2*(I.slope^2+2*I.mid^2))

theorem D₀_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |D₀ q-D₀ p| ≤ 6*|q-p| := by
  have hp2 := sq_le_one hp
  have hq2 := sq_le_one hq
  have hsum : |q+p| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith [(abs_le.mp hp).1, (abs_le.mp hq).1]
    · linarith [(abs_le.mp hp).2, (abs_le.mp hq).2]
  have hcoef0 : 0 ≤ (10+q^2+p^2)/4 := by positivity
  have hcoef3 : (10+q^2+p^2)/4 ≤ 3 := by linarith
  have hid : D₀ q-D₀ p = (q-p)*(q+p)*((10+q^2+p^2)/4) := by
    unfold D₀ G
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hcoef0]
  have hh := mul_le_mul hsum hcoef3 hcoef0 (by norm_num : (0:ℝ) ≤ 2)
  have hg := mul_le_mul_of_nonneg_left hh (abs_nonneg (q-p))
  nlinarith only [hg]

theorem midpointWeight_lipschitz (e : ℝ) {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |midpointWeight e q-midpointWeight e p| ≤ 3*e^2*|q-p| := by
  have hdq : 0 ≤ D₀ q := by unfold D₀; positivity
  have hdp : 0 ≤ D₀ p := by unfold D₀; positivity
  have hi := inv_sqrt_abs_difference (mul_nonneg (sq_nonneg e) hdq)
    (mul_nonneg (sq_nonneg e) hdp)
  have hid : |e^2*D₀ q-e^2*D₀ p| = e^2*|D₀ q-D₀ p| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg e)]
  rw [hid] at hi
  have hb := mul_le_mul_of_nonneg_left (D₀_lipschitz hp hq) (sq_nonneg e)
  unfold midpointWeight
  nlinarith only [hi, hb]

theorem Cell.secantWeight_bounds (I : Cell) (e : ℝ) :
    0 ≤ I.secantWeight e-midpointWeight e I.mid ∧
    I.secantWeight e-midpointWeight e I.mid ≤ e^2*I.width^2/8 := by
  have hg0 := G_nonneg I.mid
  have hg1 := G_le_one I.mid_abs_le
  have ha0 := I.slope_nonneg
  have hs := I.slope_mid_identity
  have hdiff : D₀ I.mid-(I.slope^2+2*I.mid^2) =
      G I.mid*I.half^2-I.half^4/4 := by
    rw [hs]
    unfold D₀
    ring
  have hd0 : 0 ≤ D₀ I.mid-(I.slope^2+2*I.mid^2) := by
    have hh : 0 ≤ G I.mid-I.half^2/4 := by nlinarith only [hs, ha0, sq_nonneg I.half]
    have hh' := mul_nonneg (sq_nonneg I.half) hh
    nlinarith only [hh', hdiff]
  have hd1 : D₀ I.mid-(I.slope^2+2*I.mid^2) ≤ I.half^2 := by
    have hh := mul_le_mul_of_nonneg_right hg1 (sq_nonneg I.half)
    nlinarith only [hh, hdiff, sq_nonneg (I.half^2)]
  have ha : 0 ≤ e^2*(I.slope^2+2*I.mid^2) := by positivity
  have hab : e^2*(I.slope^2+2*I.mid^2) ≤ e^2*D₀ I.mid := by
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg e)
  obtain ⟨h0, h1⟩ := inv_sqrt_difference ha hab
  constructor
  · exact h0
  · have hh := mul_le_mul_of_nonneg_left hd1 (sq_nonneg e)
    unfold Cell.secantWeight midpointWeight
    dsimp [Cell.half] at hh
    nlinarith only [h1, hh]

/-- A primitive for the variation of the even quartic cap shape. -/
def capVariation (q : ℝ) : ℝ := if q ≤ 0 then -h q else h q

theorem h_le_h_of_sq_le {p q : ℝ} (hpq : p^2 ≤ q^2) : h p ≤ h q := by
  have hh := mul_le_mul hpq (show 1+p^2 ≤ 1+q^2 by linarith)
    (show 0 ≤ 1+p^2 by positivity) (sq_nonneg q)
  unfold h G
  nlinarith only [hh]

theorem capVariation_controls {p q : ℝ} (hpq : p ≤ q) :
    |h q-h p| ≤ capVariation q-capVariation p := by
  by_cases hq : q ≤ 0
  · have hp : p ≤ 0 := hpq.trans hq
    have hs : q^2 ≤ p^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (show 0 ≤ -p-q by linarith)]
    have hh := h_le_h_of_sq_le hs
    simp only [capVariation, ite_eq_left hq, ite_eq_left hp, abs_of_nonpos (sub_nonpos.mpr hh)]
    linarith
  · by_cases hp : p ≤ 0
    · have hhp := h_nonneg p
      have hhq := h_nonneg q
      simp only [capVariation, ite_eq_right hq, ite_eq_left hp]
      rw [abs_le]
      constructor <;> linarith
    · have hs : p^2 ≤ q^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (show 0 ≤ p+q by linarith)]
      have hh := h_le_h_of_sq_le hs
      simp only [capVariation, ite_eq_right hq, ite_eq_right hp, abs_of_nonneg (sub_nonneg.mpr hh)]
      exact le_rfl

theorem capVariation_monotone : Monotone capVariation := by
  intro p q hpq
  have hh := capVariation_controls hpq
  linarith [abs_nonneg (h q-h p)]

theorem capVariation_endpoints : capVariation 1-capVariation (-1) = 2 := by
  norm_num [capVariation, h, G]

/-- The cell maximum loses no more than the cap variation across that cell. -/
theorem Cell.maximum_cap_error (I : Cell) (e : ℝ) {q : ℝ} (hq : I.Mem q) :
    max (C e I.left) (C e I.right)-C e q ≤
      e^2*(capVariation I.right-capVariation I.left) := by
  have hL := capVariation_controls hq.1
  have hR := capVariation_controls hq.2
  have hLm := capVariation_monotone hq.1
  have hRm := capVariation_monotone hq.2
  have hLb : h I.left-h q ≤ capVariation I.right-capVariation I.left := by
    have hab := neg_le_abs (h q-h I.left)
    linarith
  have hRb : h I.right-h q ≤ capVariation I.right-capVariation I.left := by
    have hab := le_abs_self (h I.right-h q)
    linarith
  have hLe := mul_le_mul_of_nonneg_left hLb (sq_nonneg e)
  have hRe := mul_le_mul_of_nonneg_left hRb (sq_nonneg e)
  rcases le_total (C e I.left) (C e I.right) with hc | hc
  · rw [max_eq_right hc]
    unfold C
    nlinarith only [hRe]
  · rw [max_eq_left hc]
    unfold C
    nlinarith only [hLe]

theorem linear_le_inv_sqrt {z : ℝ} (hz : 0 ≤ z) :
    1-z/2 ≤ 1/Real.sqrt (1+z) := by
  let s := Real.sqrt (1+z)
  have hs : 1 ≤ s := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+z by linarith)
    simpa [s] using hh
  have hs0 : 0 < s := by linarith
  have hs2 : s^2 = 1+z := Real.sq_sqrt (by linarith)
  change 1-z/2 ≤ 1/s
  apply (le_div_iff₀ hs0).2
  have hn := mul_nonneg (sq_nonneg (s-1)) (show 0 ≤ s+2 by linarith)
  have hid : 1-(1-z/2)*s = (s-1)^2*(s+2)/2 := by
    rw [show z = s^2-1 by linarith]
    ring
  nlinarith only [hn, hid]

theorem continuum_integrand_lower {e q : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1/10)
    (hq : q ∈ Set.Icc (-1:ℝ) 1) :
    1+e^2*(2*h q-D₀ q/2)-3*e^4 ≤
      (C e q)^2/Real.sqrt (1+e^2*D₀ q) := by
  obtain ⟨hh0, hh1⟩ := h_bounds hq
  obtain ⟨hd0, hd3⟩ := D₀_bounds hq
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he0 he1
  have hz := mul_nonneg (sq_nonneg e) hd0
  have hzu : e^2*D₀ q ≤ 3/100 := by
    exact (mul_le_mul he2 hd3 hd0 (by norm_num)).trans (by norm_num)
  have hlin0 : 0 ≤ 1-e^2*D₀ q/2 := by linarith
  have hcap : 1+2*e^2*h q ≤ (C e q)^2 := by
    have hb : 0 ≤ (9/16:ℝ)*e^4 := by positivity
    have hbase : 0 ≤ 1+e^2*h q := by positivity
    have hm := mul_nonneg hb hbase
    unfold C
    nlinarith [sq_nonneg (e^2*h q), sq_nonneg ((9/16:ℝ)*e^4)]
  have hi := mul_le_mul hcap (linear_le_inv_sqrt hz) hlin0 (sq_nonneg (C e q))
  have hprod : h q*D₀ q ≤ 3 := by
    exact (mul_le_mul hh1 hd3 hd0 (by norm_num)).trans (by norm_num)
  have hrem := mul_le_mul_of_nonneg_left hprod (pow_nonneg he0 4)
  simp only [div_eq_mul_inv, one_mul] at hi ⊢
  nlinarith only [hi, hrem]

theorem uniformPadding_ge_half {e d : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hd0 : 0 ≤ d) : e*d/2 ≤ uniformPadding e d := by
  have hM := Mstar_ge_one e
  have hfac0 : 0 ≤ 1+e/2+e*d/4 := by positivity
  have hfac : 1 ≤ 1+e/2+e*d/4 := by nlinarith [mul_nonneg he0 hd0]
  have hQ : 1-e ≤ Mstar e*(1+e/2+e*d/4)+2*e := by
    have hh := mul_le_mul hM hfac (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ Mstar e)
    nlinarith only [hh, he0]
  rw [uniformPadding_factor, le_div_iff₀ (by linarith : 0 < 2*(1-e))]
  have hh := mul_le_mul_of_nonneg_left hQ (mul_nonneg he0 hd0)
  nlinarith only [hh]

end
end TetrahedronCover
