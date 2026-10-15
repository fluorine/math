module
public import TetrahedronCover.Definitions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Generated exact polynomial certificates for reciprocal square roots.
Regenerate with tools/generate_certificates.py. All coefficients are rational;
all equalities are checked by ring and all order conclusions by proof terms. -/
namespace TetrahedronCover
noncomputable section

def taylor8 (z : ℝ) : ℝ :=
    (1 : ℝ) * z^0 +
    (-1 / 2 : ℝ) * z^1 +
    (3 / 8 : ℝ) * z^2 +
    (-5 / 16 : ℝ) * z^3 +
    (35 / 128 : ℝ) * z^4 +
    (-63 / 256 : ℝ) * z^5 +
    (231 / 1024 : ℝ) * z^6 +
    (-429 / 2048 : ℝ) * z^7 +
    (6435 / 32768 : ℝ) * z^8

private lemma taylor8_bernstein (z : ℝ) : taylor8 z =
    (1 : ℝ) * z^0 * (1-z)^8 +
    (15 / 2 : ℝ) * z^1 * (1-z)^7 +
    (199 / 8 : ℝ) * z^2 * (1-z)^6 +
    (759 / 16 : ℝ) * z^3 * (1-z)^5 +
    (7275 / 128 : ℝ) * z^4 * (1-z)^4 +
    (11193 / 256 : ℝ) * z^5 * (1-z)^3 +
    (21635 / 1024 : ℝ) * z^6 * (1-z)^2 +
    (11847 / 2048 : ℝ) * z^7 * (1-z)^1 +
    (26291 / 32768 : ℝ) * z^8 * (1-z)^0 := by
  unfold taylor8
  ring

lemma taylor8_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ taylor8 z := by
  have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz1
  rw [taylor8_bernstein]
  positivity

private lemma taylor8_residual (z : ℝ) : (1+z)*(taylor8 z)^2-1 =
  z^9 * (
    (12155 / 32768 : ℝ) * z^0 * (1-z)^8 +
    (367081 / 131072 : ℝ) * z^1 * (1-z)^7 +
    (2446249 / 262144 : ℝ) * z^2 * (1-z)^6 +
    (37461931 / 2097152 : ℝ) * z^3 * (1-z)^5 +
    (90035995 / 4194304 : ℝ) * z^4 * (1-z)^4 +
    (277820885 / 16777216 : ℝ) * z^5 * (1-z)^3 +
    (268912409 / 33554432 : ℝ) * z^6 * (1-z)^2 +
    (2371652201 / 1073741824 : ℝ) * z^7 * (1-z)^1 +
    (154345769 / 536870912 : ℝ) * z^8 * (1-z)^0) := by
  unfold taylor8
  ring

lemma taylor8_residual_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ (1+z)*(taylor8 z)^2-1 := by
  have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz1
  rw [taylor8_residual]
  positivity

def taylor9 (z : ℝ) : ℝ :=
    (1 : ℝ) * z^0 +
    (-1 / 2 : ℝ) * z^1 +
    (3 / 8 : ℝ) * z^2 +
    (-5 / 16 : ℝ) * z^3 +
    (35 / 128 : ℝ) * z^4 +
    (-63 / 256 : ℝ) * z^5 +
    (231 / 1024 : ℝ) * z^6 +
    (-429 / 2048 : ℝ) * z^7 +
    (6435 / 32768 : ℝ) * z^8 +
    (-12155 / 65536 : ℝ) * z^9

private lemma taylor9_bernstein (z : ℝ) : taylor9 z =
    (1 : ℝ) * z^0 * (1-z)^9 +
    (17 / 2 : ℝ) * z^1 * (1-z)^8 +
    (259 / 8 : ℝ) * z^2 * (1-z)^7 +
    (1157 / 16 : ℝ) * z^3 * (1-z)^6 +
    (13347 / 128 : ℝ) * z^4 * (1-z)^5 +
    (25743 / 256 : ℝ) * z^5 * (1-z)^4 +
    (66407 / 1024 : ℝ) * z^6 * (1-z)^3 +
    (55117 / 2048 : ℝ) * z^7 * (1-z)^2 +
    (215843 / 32768 : ℝ) * z^8 * (1-z)^1 +
    (40427 / 65536 : ℝ) * z^9 * (1-z)^0 := by
  unfold taylor9
  ring

lemma taylor9_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ taylor9 z := by
  have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz1
  rw [taylor9_bernstein]
  positivity

private lemma taylor9_residual (z : ℝ) : 1-(1+z)*(taylor9 z)^2 =
  z^10 * (
    (46189 / 131072 : ℝ) * z^0 * (1-z)^9 +
    (197353 / 65536 : ℝ) * z^1 * (1-z)^8 +
    (24148449 / 2097152 : ℝ) * z^2 * (1-z)^7 +
    (54111221 / 2097152 : ℝ) * z^3 * (1-z)^6 +
    (625870317 / 16777216 : ℝ) * z^4 * (1-z)^5 +
    (37810703 / 1048576 : ℝ) * z^5 * (1-z)^4 +
    (25015904583 / 1073741824 : ℝ) * z^6 * (1-z)^3 +
    (10404686957 / 1073741824 : ℝ) * z^7 * (1-z)^2 +
    (10162956607 / 4294967296 : ℝ) * z^8 * (1-z)^1 +
    (513141319 / 2147483648 : ℝ) * z^9 * (1-z)^0) := by
  unfold taylor9
  ring

lemma taylor9_residual_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ 1-(1+z)*(taylor9 z)^2 := by
  have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz1
  rw [taylor9_residual]
  positivity

lemma inverse_sqrt_bounds {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    taylor9 z ≤ 1 / Real.sqrt (1+z) ∧
    1 / Real.sqrt (1+z) ≤ taylor8 z := by
  have hp : 0 < 1+z := by linarith
  have hs : 0 < Real.sqrt (1+z) := Real.sqrt_pos.mpr hp
  have hs2 : (Real.sqrt (1+z))^2 = 1+z := Real.sq_sqrt hp.le
  have h8 := taylor8_nonneg hz hz1
  have h9 := taylor9_nonneg hz hz1
  have r8 := taylor8_residual_nonneg hz hz1
  have r9 := taylor9_residual_nonneg hz hz1
  have sq8 : 1 ≤ (taylor8 z * Real.sqrt (1+z))^2 := by
    rw [mul_pow, hs2]
    nlinarith only [r8]
  have sq9 : (taylor9 z * Real.sqrt (1+z))^2 ≤ 1 := by
    rw [mul_pow, hs2]
    nlinarith only [r9]
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith only [sq9, mul_nonneg h9 hs.le]
  · apply (div_le_iff₀ hs).mpr
    nlinarith only [sq8, mul_nonneg h8 hs.le]

end
end TetrahedronCover
