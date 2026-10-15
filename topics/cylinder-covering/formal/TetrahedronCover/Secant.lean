module

public import TetrahedronCover.Algebra
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ByContra

/-!
The finite-secant perturbation bound and the exact overlap contradiction.
No mesh regularity is assumed: every pair of positive-width cells in [-1,1]
is covered by the same explicit buffer.  This is the algebraic core of the
closed-body coverage theorem in Geometry.lean.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section

/-- The physical lower-radius weight in equation (9). -/
def rhoWeight (e : ℝ) (I J : Cell) (q : ℝ) : ℝ :=
  1-e*q*J.mid+e^2*J.slope*I.boundary q
/-- The physical upper-radius weight in equation (9). -/
def sigmaWeight (e : ℝ) (I J : Cell) (p : ℝ) : ℝ :=
  1+e*p*I.mid+e^2*I.slope*J.boundary p
/-- The determinant of the two coupled intercept equations. -/
def secantDenom (e : ℝ) (I J : Cell) : ℝ := 1+e^2*I.slope*J.slope

def weightError (e : ℝ) (I J : Cell) : ℝ :=
  e*J.half+e^2/2*(J.half+I.half^2)

private lemma abs_product_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a*b| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

lemma rhoWeight_ge {e q : ℝ} (I J : Cell) (he : 0 ≤ e) (hq : I.Mem q) :
    1-e ≤ rhoWeight e I J q := by
  have hp : |q*J.mid| ≤ 1 := by
    simpa using abs_product_le (Cell.mem_abs_le hq) J.mid_abs_le
  have hlin : e*q*J.mid ≤ e := by
    have hh := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hp) he
    nlinarith
  have hpos : 0 ≤ e^2*J.slope*I.boundary q :=
    mul_nonneg (mul_nonneg (sq_nonneg _) J.slope_nonneg) (Cell.boundary_nonneg hq)
  unfold rhoWeight
  linarith

lemma sigmaWeight_ge {e p : ℝ} (I J : Cell) (he : 0 ≤ e) (hp : J.Mem p) :
    1-e ≤ sigmaWeight e I J p := by
  have hprod : |p*I.mid| ≤ 1 := by
    simpa using abs_product_le (Cell.mem_abs_le hp) I.mid_abs_le
  have hlin : -e ≤ e*p*I.mid := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hprod).1 he
    nlinarith
  have hpos : 0 ≤ e^2*I.slope*J.boundary p :=
    mul_nonneg (mul_nonneg (sq_nonneg _) I.slope_nonneg) (Cell.boundary_nonneg hp)
  unfold sigmaWeight
  linarith

lemma weightError_nonneg {e : ℝ} (I J : Cell) (he : 0 ≤ e) :
    0 ≤ weightError e I J := by
  unfold weightError
  have := J.half_nonneg
  positivity

private lemma linear_error {e p q : ℝ} (I J : Cell) (he : 0 ≤ e)
    (hq : I.Mem q) (hp : J.Mem p) :
    |e*q*(J.mid-p)| ≤ e*J.half := by
  have hmid : |J.mid-p| ≤ J.half := by
    rw [abs_sub_comm]
    exact Cell.abs_sub_mid_le_half hp
  have habs : |q*(J.mid-p)| ≤ J.half := by
    simpa using abs_product_le (Cell.mem_abs_le hq) hmid
  have hh := mul_le_mul_of_nonneg_left habs he
  simpa only [abs_mul, abs_of_nonneg he, mul_assoc] using hh

private lemma quadratic_error {p q : ℝ} (I J : Cell)
    (hq : I.Mem q) (hp : J.Mem p) :
    |J.slope*I.boundary q-G p*D q| ≤ (J.half+I.half^2)/2 := by
  have hD : |D q| ≤ (1/2 : ℝ) := by
    rw [abs_of_nonneg (D_nonneg (Cell.mem_abs_le hq))]
    exact D_le_half q
  have hA : |J.slope| ≤ 1 := by
    rw [abs_of_nonneg J.slope_nonneg]
    exact J.slope_le_one
  have hE : |I.error q| ≤ I.half^2/2 := by
    rw [abs_of_nonneg (Cell.error_nonneg hq)]
    exact I.error_le_half_sq q
  have hfirst := abs_product_le (Cell.abs_slope_sub_G hp) hD
  have hsecond := abs_product_le hA hE
  have hid : J.slope*I.boundary q-G p*D q =
      (J.slope-G p)*D q-J.slope*I.error q := by
    rw [I.boundary_error q]
    ring
  rw [hid]
  have htri := abs_sub ((J.slope-G p)*D q) (J.slope*I.error q)
  linarith

/-- The first inequality in (13), with the full second-order cell error. -/
lemma rhoWeight_error {e p q : ℝ} (I J : Cell) (he : 0 ≤ e)
    (hq : I.Mem q) (hp : J.Mem p) :
    |rhoWeight e I J q-Aminus e p q| ≤ weightError e I J := by
  have hlin := linear_error I J he hq hp
  have hquad := quadratic_error I J hq hp
  have hquad2 : |e^2*(J.slope*I.boundary q-G p*D q)| ≤
      e^2*((J.half+I.half^2)/2) := by
    simpa only [abs_mul, abs_of_nonneg (sq_nonneg e)] using
      mul_le_mul_of_nonneg_left hquad (sq_nonneg e)
  have hid : rhoWeight e I J q-Aminus e p q =
      -(e*q*(J.mid-p))+e^2*(J.slope*I.boundary q-G p*D q) := by
    unfold rhoWeight Aminus
    ring
  rw [hid]
  have htri := abs_add_le (-(e*q*(J.mid-p)))
    (e^2*(J.slope*I.boundary q-G p*D q))
  rw [abs_neg] at htri
  unfold weightError
  nlinarith

/-- The second inequality in (13). -/
lemma sigmaWeight_error {e p q : ℝ} (I J : Cell) (he : 0 ≤ e)
    (hq : I.Mem q) (hp : J.Mem p) :
    |sigmaWeight e I J p-Bplus e p q| ≤ weightError e J I := by
  have hlin := linear_error J I he hp hq
  have hquad := quadratic_error J I hp hq
  have hquad2 : |e^2*(I.slope*J.boundary p-G q*D p)| ≤
      e^2*((I.half+J.half^2)/2) := by
    simpa only [abs_mul, abs_of_nonneg (sq_nonneg e)] using
      mul_le_mul_of_nonneg_left hquad (sq_nonneg e)
  have hid : sigmaWeight e I J p-Bplus e p q =
      e*p*(I.mid-q)+e^2*(I.slope*J.boundary p-G q*D p) := by
    unfold sigmaWeight Bplus
    ring
  rw [hid]
  have htri := abs_add_le (e*p*(I.mid-q))
    (e^2*(I.slope*J.boundary p-G q*D p))
  unfold weightError
  nlinarith

/-- Determinant perturbation, equation (14). -/
lemma secantDenom_error {e p q : ℝ} (I J : Cell)
    (hq : I.Mem q) (hp : J.Mem p) :
    |secantDenom e I J-Nzero e p q| ≤ e^2*(I.half+J.half) := by
  have hA : |J.slope| ≤ 1 := by
    rw [abs_of_nonneg J.slope_nonneg]
    exact J.slope_le_one
  have hG : |G q| ≤ 1 := by
    rw [abs_of_nonneg (G_nonneg q)]
    exact G_le_one (Cell.mem_abs_le hq)
  have hfirst := abs_product_le (Cell.abs_slope_sub_G hq) hA
  have hsecond := abs_product_le hG (Cell.abs_slope_sub_G hp)
  have habs : |I.slope*J.slope-G p*G q| ≤ I.half+J.half := by
    have hid : I.slope*J.slope-G p*G q =
        (I.slope-G q)*J.slope+G q*(J.slope-G p) := by ring
    rw [hid]
    have htri := abs_add_le ((I.slope-G q)*J.slope) (G q*(J.slope-G p))
    linarith
  have hid : secantDenom e I J-Nzero e p q =
      e^2*(I.slope*J.slope-G p*G q) := by
    unfold secantDenom Nzero
    ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg e)]
  exact mul_le_mul_of_nonneg_left habs (sq_nonneg e)

private lemma weighted_error {w a c E M : ℝ} (habs : |w-a| ≤ E)
    (hc : 0 ≤ c) (hcM : c ≤ M) (hE : 0 ≤ E) :
    -M*E ≤ w*c-a*c := by
  have hlow := mul_le_mul_of_nonneg_right (abs_le.mp habs).1 hc
  have hbound := mul_le_mul_of_nonneg_left hcM hE
  nlinarith

/-- The explicit unbuffered error (15), valid for arbitrary positive cells. -/
theorem unbuffered_weighted {e p q : ℝ} (I J : Cell) (he : 0 ≤ e)
    (hq : I.Mem q) (hp : J.Mem p) :
    -(K₀ e*(I.half+J.half)+(Mstar e*e^2/2)*(I.half^2+J.half^2)) ≤
      rhoWeight e I J q*C e q+sigmaWeight e I J p*C e p-2*secantDenom e I J := by
  have hc := continuous_certificate e p q (Cell.mem_abs_le hp) (Cell.mem_abs_le hq)
  have hr := weighted_error (rhoWeight_error I J he hq hp) (C_pos e q).le
    (C_le_Mstar e (Cell.mem_abs_le hq)) (weightError_nonneg I J he)
  have hs := weighted_error (sigmaWeight_error I J he hq hp) (C_pos e p).le
    (C_le_Mstar e (Cell.mem_abs_le hp)) (weightError_nonneg J I he)
  have hd := (abs_le.mp (secantDenom_error I J (e := e) hq hp)).2
  have herr : Mstar e*weightError e I J+Mstar e*weightError e J I+
      2*(e^2*(I.half+J.half)) =
      K₀ e*(I.half+J.half)+(Mstar e*e^2/2)*(I.half^2+J.half^2) := by
    unfold weightError K₀
    ring
  linarith

lemma Cell.padding_identity (I : Cell) {e : ℝ} (he1 : e < 1) :
    (1-e)*I.padding e = K₀ e*I.half+(Mstar e*e^2/2)*I.half^2 := by
  unfold Cell.padding
  have hh : 1-e ≠ 0 := by linarith
  field_simp

/-- The buffered weights dominate the exact determinant, equation (16). -/
theorem buffered_weighted {e p q : ℝ} (I J : Cell) (he : 0 < e) (he1 : e < 1)
    (hq : I.Mem q) (hp : J.Mem p) :
    2*secantDenom e I J ≤ rhoWeight e I J q*I.cap e+sigmaWeight e I J p*J.cap e := by
  have hr := rhoWeight_ge I J he.le hq
  have hs := sigmaWeight_ge I J he.le hp
  have hr0 : 0 ≤ rhoWeight e I J q := by linarith
  have hs0 : 0 ≤ sigmaWeight e I J p := by linarith
  have hcapI := mul_le_mul_of_nonneg_left (Cell.cap_ge (e := e) hq) hr0
  have hcapJ := mul_le_mul_of_nonneg_left (Cell.cap_ge (e := e) hp) hs0
  have hpadI := mul_le_mul_of_nonneg_right hr (I.padding_nonneg he.le he1)
  have hpadJ := mul_le_mul_of_nonneg_right hs (J.padding_nonneg he.le he1)
  have hbuf := unbuffered_weighted I J he.le hq hp
  have hidentity : (1-e)*(I.padding e+J.padding e) =
      K₀ e*(I.half+J.half)+(Mstar e*e^2/2)*(I.half^2+J.half^2) := by
    rw [mul_add, I.padding_identity he1, J.padding_identity he1]
    ring
  linarith only [hcapI, hcapJ, hpadI, hpadJ, hbuf, hidentity]

/-- The weighted sum follows algebraically from the three physical relations. -/
theorem coupled_weighted_identity (I J : Cell) {e p q X Y rho sigma : ℝ}
    (hy : Y = rho*q+e*X*I.slope)
    (hx : X = sigma*p-e*Y*J.slope)
    (hsum : rho+sigma = 2+e*(Y*J.mid-X*I.mid)) :
    rhoWeight e I J q*rho+sigmaWeight e I J p*sigma = 2*secantDenom e I J := by
  unfold rhoWeight sigmaWeight secantDenom Cell.boundary
  linear_combination (1+e^2*I.slope*J.slope)*hsum +
    e*(J.mid+e*J.slope*I.mid)*hy + e*(e*I.slope*J.mid-I.mid)*hx

/--
No simultaneous failure is possible.  This theorem is independent of the
angular selection argument: it applies to any real radii and coordinates
satisfying the exact coupled equations, so positivity assumptions about the
selected radii are not smuggled into the overlap certificate.
-/
theorem secant_overlap (I J : Cell) {e p q X Y rho sigma : ℝ}
    (he : 0 < e) (he1 : e < 1) (hq : I.Mem q) (hp : J.Mem p)
    (hy : Y = rho*q+e*X*I.slope)
    (hx : X = sigma*p-e*Y*J.slope)
    (hsum : rho+sigma = 2+e*(Y*J.mid-X*I.mid)) :
    rho ≤ I.cap e ∨ sigma ≤ J.cap e := by
  by_contra! hmiss
  have hr : 0 < rhoWeight e I J q := by linarith [rhoWeight_ge I J he.le hq]
  have hs : 0 < sigmaWeight e I J p := by linarith [sigmaWeight_ge I J he.le hp]
  have hltI := mul_lt_mul_of_pos_left hmiss.1 hr
  have hltJ := mul_lt_mul_of_pos_left hmiss.2 hs
  have hbound := buffered_weighted I J he he1 hq hp
  have heq := coupled_weighted_identity I J hy hx hsum
  linarith

end
end TetrahedronCover
