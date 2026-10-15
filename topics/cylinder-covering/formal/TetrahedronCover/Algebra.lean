module

public import TetrahedronCover.Definitions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
The polynomial certificate behind the improved quartic cap.  The sign in the
completed square is the physical-coordinate sign used by the secant axes.
Everything in this file is a theorem over the real numbers, checked by Lean's
kernel; in particular the large identity is proved by `ring`, not by sampling.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section

lemma sq_le_one {q : ℝ} (hq : |q| ≤ 1) : q^2 ≤ 1 := by
  have hs := sq_le_sq' (abs_le.mp hq).1 (abs_le.mp hq).2
  simpa only [one_pow] using hs

lemma G_nonneg (q : ℝ) : 0 ≤ G q := by unfold G; positivity
lemma G_le_one {q : ℝ} (hq : |q| ≤ 1) : G q ≤ 1 := by
  unfold G
  linarith [sq_le_one hq]
lemma D_nonneg {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ D q := by
  unfold D
  linarith [sq_le_one hq]
lemma D_le_half (q : ℝ) : D q ≤ 1/2 := by
  unfold D
  nlinarith [sq_nonneg q]
lemma h_nonneg (q : ℝ) : 0 ≤ h q := mul_nonneg (sq_nonneg q) (G_nonneg q)
lemma h_le_one {q : ℝ} (hq : |q| ≤ 1) : h q ≤ 1 := by
  unfold h
  calc
    q^2 * G q ≤ 1 * 1 := mul_le_mul (sq_le_one hq) (G_le_one hq)
      (G_nonneg q) (by norm_num)
    _ = 1 := by ring

lemma C_ge_one (e q : ℝ) : 1 ≤ C e q := by
  unfold C
  have := mul_nonneg (sq_nonneg e) (h_nonneg q)
  nlinarith [pow_nonneg (sq_nonneg e) 2]
lemma C_pos (e q : ℝ) : 0 < C e q := lt_of_lt_of_le zero_lt_one (C_ge_one e q)
lemma C_le_Mstar (e : ℝ) {q : ℝ} (hq : |q| ≤ 1) : C e q ≤ Mstar e := by
  have hb := mul_le_mul_of_nonneg_left (h_le_one hq) (sq_nonneg e)
  unfold C Mstar
  linarith
lemma Mstar_ge_one (e : ℝ) : 1 ≤ Mstar e := by
  unfold Mstar
  nlinarith [sq_nonneg e, sq_nonneg (e^2)]
lemma Mstar_pos (e : ℝ) : 0 < Mstar e := lt_of_lt_of_le zero_lt_one (Mstar_ge_one e)
lemma K₀_nonneg {e : ℝ} (he : 0 ≤ e) : 0 ≤ K₀ e := by
  unfold K₀
  have := Mstar_pos e
  positivity

lemma C_le_C_of_sq_le {e q r : ℝ} (hqr : q^2 ≤ r^2) : C e q ≤ C e r := by
  have hprod : q^2 * (1+q^2) ≤ r^2 * (1+r^2) :=
    mul_le_mul hqr (by linarith) (by positivity) (sq_nonneg r)
  have hh : h q ≤ h r := by unfold h G; nlinarith
  have hc := mul_le_mul_of_nonneg_left hh (sq_nonneg e)
  unfold C
  linarith

def Aminus (e p q : ℝ) : ℝ := 1-e*p*q+e^2*G p*D q
def Bplus (e p q : ℝ) : ℝ := 1+e*p*q+e^2*G q*D p
def Nzero (e p q : ℝ) : ℝ := 1+e^2*G p*G q

/-- Exact identity (11) of the manuscript, with the physical sign. -/
theorem quartic_identity (e p q : ℝ) :
    Aminus e p q * C e q + Bplus e p q * C e p - 2*Nzero e p q =
      e^2/2 * (p^2-q^2+e*p*q*(1+p^2+q^2)/2)^2 +
      e^4 * (G p*G q*(p^2*D p+q^2*D q) +
        (9-p^2*q^2*(1+p^2+q^2)^2)/8) +
      (9/16 : ℝ)*e^6*(G p*D q+G q*D p) := by
  unfold Aminus Bplus Nzero C h G D
  ring

/-- The quartic certificate is nonnegative throughout the full parameter box. -/
theorem continuous_certificate (e p q : ℝ) (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    2*Nzero e p q ≤ Aminus e p q*C e q + Bplus e p q*C e p := by
  have hp2 := sq_le_one hp
  have hq2 := sq_le_one hq
  have hpq : p^2*q^2 ≤ 1 := by
    calc
      p^2*q^2 ≤ 1*1 := mul_le_mul hp2 hq2 (sq_nonneg q) (by norm_num)
      _ = 1 := by ring
  have hs0 : 0 ≤ 1+p^2+q^2 := by positivity
  have hs3 : 1+p^2+q^2 ≤ 3 := by linarith
  have hs9 : (1+p^2+q^2)^2 ≤ 9 := by nlinarith
  have hprod : p^2*q^2*(1+p^2+q^2)^2 ≤ 9 := by
    calc
      p^2*q^2*(1+p^2+q^2)^2 ≤ 1*9 :=
        mul_le_mul hpq hs9 (sq_nonneg _) (by norm_num)
      _ = 9 := by ring
  have hGp := G_nonneg p
  have hGq := G_nonneg q
  have hDp := D_nonneg hp
  have hDq := D_nonneg hq
  have hrem : 0 ≤ (9-p^2*q^2*(1+p^2+q^2)^2)/8 := by linarith
  have hmain : 0 ≤
      e^2/2 * (p^2-q^2+e*p*q*(1+p^2+q^2)/2)^2 +
      e^4 * (G p*G q*(p^2*D p+q^2*D q) +
        (9-p^2*q^2*(1+p^2+q^2)^2)/8) +
      (9/16 : ℝ)*e^6*(G p*D q+G q*D p) := by positivity
  linarith [quartic_identity e p q]

namespace Cell

lemma left_abs_le (I : Cell) : |I.left| ≤ 1 := by
  rw [abs_le]
  exact ⟨I.left_ge, le_trans I.strict.le I.right_le⟩
lemma right_abs_le (I : Cell) : |I.right| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_trans I.left_ge I.strict.le, I.right_le⟩
lemma mem_abs_le {I : Cell} {q : ℝ} (hq : I.Mem q) : |q| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_trans I.left_ge hq.1, le_trans hq.2 I.right_le⟩
lemma half_pos (I : Cell) : 0 < I.half := by unfold half width; linarith [I.strict]
lemma half_nonneg (I : Cell) : 0 ≤ I.half := (half_pos I).le
lemma half_le_one (I : Cell) : I.half ≤ 1 := by
  unfold half width
  linarith [I.left_ge, I.right_le]
lemma mid_mem (I : Cell) : I.Mem I.mid := by
  unfold Mem mid
  constructor <;> linarith [I.strict]
lemma mid_abs_le (I : Cell) : |I.mid| ≤ 1 := mem_abs_le I.mid_mem
lemma abs_mid_add_half (I : Cell) : |I.mid| + I.half ≤ 1 := by
  unfold mid half width
  rcases le_total 0 ((I.left+I.right)/2) with hm | hm
  · rw [abs_of_nonneg hm]
    linarith [I.right_le]
  · rw [abs_of_nonpos hm]
    linarith [I.left_ge]
lemma abs_sub_mid_le_half {I : Cell} {q : ℝ} (hq : I.Mem q) : |q-I.mid| ≤ I.half := by
  rw [abs_le]
  unfold mid half width
  constructor <;> linarith [hq.1, hq.2]
lemma slope_nonneg (I : Cell) : 0 ≤ I.slope := by
  have hab : |I.left*I.right| ≤ 1 := by
    rw [abs_mul]
    calc
      |I.left| * |I.right| ≤ 1*1 :=
        mul_le_mul I.left_abs_le I.right_abs_le (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  unfold slope
  linarith [(abs_le.mp hab).1]
lemma slope_le_one (I : Cell) : I.slope ≤ 1 := by
  have hab : |I.left*I.right| ≤ 1 := by
    rw [abs_mul]
    calc
      |I.left| * |I.right| ≤ 1*1 :=
        mul_le_mul I.left_abs_le I.right_abs_le (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  unfold slope
  linarith [(abs_le.mp hab).2]
lemma slope_mid_identity (I : Cell) : I.slope = G I.mid-I.half^2/2 := by
  unfold slope G mid half width
  ring
lemma boundary_left (I : Cell) : I.boundary I.left = D I.left := by
  unfold boundary slope mid D
  ring
lemma boundary_right (I : Cell) : I.boundary I.right = D I.right := by
  unfold boundary slope mid D
  ring
lemma boundary_nonneg {I : Cell} {q : ℝ} (hq : I.Mem q) : 0 ≤ I.boundary q := by
  rcases le_total 0 I.mid with hm | hm
  · have hprod := mul_nonneg (sub_nonneg.mpr hq.2) hm
    have hr := D_nonneg I.right_abs_le
    rw [← I.boundary_right] at hr
    unfold boundary at *
    nlinarith
  · have hprod := mul_nonneg (sub_nonneg.mpr hq.1) (neg_nonneg.mpr hm)
    have hl := D_nonneg I.left_abs_le
    rw [← I.boundary_left] at hl
    unfold boundary at *
    nlinarith

/-- The exact loss of a secant's interpolated boundary from the parabola. -/
def error (I : Cell) (q : ℝ) : ℝ := (I.half^2-(q-I.mid)^2)/2
lemma boundary_error (I : Cell) (q : ℝ) : I.boundary q = D q-I.error q := by
  unfold boundary error
  rw [I.slope_mid_identity]
  unfold G D
  ring
lemma error_nonneg {I : Cell} {q : ℝ} (hq : I.Mem q) : 0 ≤ I.error q := by
  have hb := abs_sub_mid_le_half hq
  have ha := I.half_nonneg
  have hsq : (q-I.mid)^2 ≤ I.half^2 := by
    exact sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  unfold error
  linarith
lemma error_le_half_sq (I : Cell) (q : ℝ) : I.error q ≤ I.half^2/2 := by
  unfold error
  nlinarith [sq_nonneg (q-I.mid)]
lemma abs_slope_sub_G {I : Cell} {q : ℝ} (hq : I.Mem q) : |I.slope-G q| ≤ I.half := by
  have hb := abs_sub_mid_le_half hq
  have ha := I.half_nonneg
  have hm := I.abs_mid_add_half
  have hsq : (q-I.mid)^2 ≤ I.half^2 := by
    exact sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have hid : I.slope-G q = -(I.mid*(q-I.mid)) -
      (I.half^2+(q-I.mid)^2)/2 := by
    rw [I.slope_mid_identity]
    unfold G
    ring
  rw [hid]
  calc
    |-(I.mid*(q-I.mid))-(I.half^2+(q-I.mid)^2)/2| ≤
        |I.mid| * |q-I.mid|+(I.half^2+(q-I.mid)^2)/2 := by
      have htri := abs_sub (-(I.mid*(q-I.mid))) ((I.half^2+(q-I.mid)^2)/2)
      simpa only [abs_neg, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (I.half^2+(q-I.mid)^2)/2)] using htri
    _ ≤ |I.mid| * I.half+I.half^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg I.mid)]
    _ ≤ I.half := by
      nlinarith [mul_le_mul_of_nonneg_right hm ha]

lemma C_le_endpoint_max {I : Cell} {e q : ℝ} (hq : I.Mem q) :
    C e q ≤ max (C e I.left) (C e I.right) := by
  rcases le_total q 0 with hq0 | hq0
  · have hs : q^2 ≤ I.left^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq.1) (by linarith [hq.1] : 0 ≤ -q-I.left)]
    exact le_trans (C_le_C_of_sq_le hs) (le_max_left _ _)
  · have hs : q^2 ≤ I.right^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq.2) (by linarith [hq.2] : 0 ≤ I.right+q)]
    exact le_trans (C_le_C_of_sq_le hs) (le_max_right _ _)
lemma cap_ge {I : Cell} {e q : ℝ} (hq : I.Mem q) :
    C e q+I.padding e ≤ I.cap e := by
  unfold cap
  exact add_le_add (C_le_endpoint_max (e := e) hq) le_rfl
lemma cap_le_Mstar_add_padding (I : Cell) (e : ℝ) :
    I.cap e ≤ Mstar e+I.padding e := by
  unfold cap
  exact add_le_add (max_le (C_le_Mstar e I.left_abs_le)
    (C_le_Mstar e I.right_abs_le)) le_rfl
lemma padding_nonneg (I : Cell) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) :
    0 ≤ I.padding e := by
  unfold padding
  have := I.half_nonneg
  have := K₀_nonneg he
  have := Mstar_pos e
  have : 0 ≤ 1-e := by linarith
  positivity
lemma cap_pos (I : Cell) {e : ℝ} (he : 0 < e) (he1 : e < 1) : 0 < I.cap e := by
  have hcap := cap_ge I.mid_mem (e := e)
  have hpad := I.padding_nonneg he.le he1
  linarith [C_pos e I.mid]

end Cell
end
end TetrahedronCover
