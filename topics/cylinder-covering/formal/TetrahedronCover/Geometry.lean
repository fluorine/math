module

public import TetrahedronCover.Partition
public import TetrahedronCover.Secant
public import OAI.Geometry.TriangularCovering.Shadows

/-! The scalar secant construction as actual Euclidean triangular cylinders.

All bases below are orthogonal projections of nondegenerate closed triangles.
The imported `TriCylinder` structure records their compactness, convexity,
measurability, perpendicularity, and finite Euclidean area. Coverage is of the
whole closed regular tetrahedron, including its faces, edges, and vertices.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section
open OAI.TriangularCovering
open scoped BigOperators InnerProductSpace

/-- The physical lower cap is half the scalar cap. -/
def lowerFamily (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (i : Fin P.count) : TriCylinder :=
  lowerCylinder (P.cell i).strict
    (div_pos ((P.cell i).cap_pos he he1) (by norm_num : (0 : ℝ) < 2))
    e (P.cell i).slope (P.cell i).mid

/-- The upper family is the quarter-turn counterpart of the lower family. -/
def upperFamily (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (i : Fin P.count) : TriCylinder :=
  upperCylinder (P.cell i).strict
    (div_pos ((P.cell i).cap_pos he he1) (by norm_num : (0 : ℝ) < 2))
    e (P.cell i).slope (P.cell i).mid

/-- Exactly two cylinders per positive partition cell, counted with multiplicity. -/
def finiteFamily (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    Fin (2 * P.count) → TriCylinder :=
  (Fin.append (lowerFamily P e he he1) (upperFamily P e he he1)) ∘
    Fin.cast (two_mul P.count)

/-- Selection and secant overlap, before the final physical-cylinder bridge. -/
theorem coordinate_coverage (P : Partition) {e x y t : ℝ}
    (he : 0 < e) (he1 : e < 1) (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ i : Fin P.count, ∃ q : ℝ, (P.cell i).Mem q ∧
      0 ≤ t - e * x * (P.cell i).mid ∧
      t - e * x * (P.cell i).mid ≤ (P.cell i).cap e / 2 ∧
      y = (t - e * x * (P.cell i).mid) * q + e * x * (P.cell i).slope) ∨
    (∃ i : Fin P.count, ∃ p : ℝ, (P.cell i).Mem p ∧
      0 ≤ 1 - t + e * y * (P.cell i).mid ∧
      1 - t + e * y * (P.cell i).mid ≤ (P.cell i).cap e / 2 ∧
      x = (1 - t + e * y * (P.cell i).mid) * p - e * y * (P.cell i).slope) := by
  obtain ⟨i, q, hq, hr, hy'⟩ := P.angular_selection (ell := e * x) hy
  obtain ⟨j, p, hp, hs, hx'⟩ := P.angular_selection (ell := -(e * y)) hx
  have hs' : 0 ≤ 1 - t + e * y * (P.cell j).mid := by
    simpa only [neg_mul, sub_neg_eq_add] using hs
  have hx'' : x = (1 - t + e * y * (P.cell j).mid) * p -
      e * y * (P.cell j).slope := by
    linear_combination hx'
  have hcuts := secant_overlap (P.cell i) (P.cell j)
    (X := 2*x) (Y := 2*y)
    (rho := 2*(t-e*x*(P.cell i).mid))
    (sigma := 2*(1-t+e*y*(P.cell j).mid)) he he1 hq hp
    (by linear_combination 2 * hy')
    (by linear_combination 2 * hx'')
    (by ring)
  rcases hcuts with hl | hu
  · exact Or.inl ⟨i, q, hq, hr, by linarith only [hl], hy'⟩
  · exact Or.inr ⟨j, p, hp, hs', by linarith only [hu], hx''⟩

/-- Every point of the closed body belongs to at least one constructed cylinder.
There is no smallness condition beyond `0 < e < 1`, and no positive-radius
assumption: the first-crossing theorem includes zero radii. -/
theorem finiteFamily_covers (P : Partition) {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    Covers (finiteFamily P e he he1) := by
  rintro z ⟨x, y, t, _ht0, _ht1, hx, hy, rfl⟩
  rcases coordinate_coverage P he he1 hx hy with
    ⟨i, q, hq, hr, hcap, hy'⟩ | ⟨i, p, hp, hs, hcap, hx'⟩
  · refine ⟨Fin.cast (two_mul P.count).symm (Fin.castAdd P.count i), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_left]
    apply lowerCylinder_hit _ _ _ _ _ _ _ _ hr hcap
    · have hl := mul_le_mul_of_nonneg_right hq.1 hr
      nlinarith only [hl, hy']
    · have hu := mul_le_mul_of_nonneg_right hq.2 hr
      nlinarith only [hu, hy']
  · refine ⟨Fin.cast (two_mul P.count).symm (Fin.natAdd P.count i), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_right]
    apply upperCylinder_hit _ _ _ _ _ _ _ _ hs hcap
    · have hl := mul_le_mul_of_nonneg_right hp.1 hs
      nlinarith only [hl, hx']
    · have hu := mul_le_mul_of_nonneg_right hp.2 hs
      nlinarith only [hu, hx']

/-- Exact geometric area identity, with both cylinder families included. -/
theorem finiteFamily_total_H (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    totalArea (finiteFamily P e he he1) / H =
      ∑ i : Fin P.count, (P.cell i).term e := by
  have hs : totalArea (finiteFamily P e he he1) =
      (∑ i : Fin P.count, area (lowerFamily P e he he1 i).base) +
      (∑ i : Fin P.count, area (upperFamily P e he he1 i).base) := by
    change (∑ i : Fin (2 * P.count),
      (fun k : Fin (P.count + P.count) =>
        area (Fin.append (lowerFamily P e he he1) (upperFamily P e he he1) k).base)
        ((finCongr (two_mul P.count)) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul P.count))
      (fun k => area (Fin.append (lowerFamily P e he he1) (upperFamily P e he he1) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [lowerFamily, upperFamily, lowerCylinder_area, upperCylinder_area]
  dsimp [Cell.term, Cell.width]
  field_simp [H_ne_zero]
  ring

/-- Normalization is the true minimum planar projection area of the body. -/
theorem finiteFamily_total (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    totalArea (finiteFamily P e he he1) / A_min =
      ∑ i : Fin P.count, (P.cell i).term e := by
  rw [projection_minimum]
  exact finiteFamily_total_H P e he he1

/-- The actual bases are compact, perpendicular nondegenerate triangles. -/
theorem finiteFamily_bases (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (i : Fin (2 * P.count)) :
    IsCompact (finiteFamily P e he he1 i).base ∧
    (∀ z ∈ (finiteFamily P e he he1 i).base,
      inner ℝ (finiteFamily P e he he1 i).axis z = 0) ∧
    ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧
      (finiteFamily P e he he1 i).base = convexHull ℝ (Set.range v) :=
  ⟨(finiteFamily P e he he1 i).compact,
    (finiteFamily P e he he1 i).perpendicular,
    (finiteFamily P e he he1 i).triangular⟩

/-- Tangent of the unoriented axis angle from the horizontal x-axis, computed
from the actual unit axis of the cylinder. The denominator is nonzero for every
lower cylinder in this construction. -/
def lowerAxisTangent (c : TriCylinder) : ℝ :=
  Real.sqrt ((c.axis 1 / c.axis 0)^2 + (c.axis 2 / c.axis 0)^2)

/-- Tangent of the unoriented axis angle from the horizontal y-axis. -/
def upperAxisTangent (c : TriCylinder) : ℝ :=
  Real.sqrt ((c.axis 0 / c.axis 1)^2 + (c.axis 2 / c.axis 1)^2)

theorem lowerFamily_axis_nonzero (P : Partition) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (i : Fin P.count) :
    (lowerFamily P e he he1 i).axis 0 ≠ 0 := by
  change ‖tiltV e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1 ≠ 0
  simpa using inv_ne_zero (norm_ne_zero_iff.mpr
    (tiltV_ne_zero e (P.cell i).slope (P.cell i).mid))

theorem upperFamily_axis_nonzero (P : Partition) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (i : Fin P.count) :
    (upperFamily P e he he1 i).axis 1 ≠ 0 := by
  change ‖tiltW e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1 ≠ 0
  simpa using inv_ne_zero (norm_ne_zero_iff.mpr
    (tiltW_ne_zero e (P.cell i).slope (P.cell i).mid))

theorem lowerFamily_axisTangent (P : Partition) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (i : Fin P.count) :
    lowerAxisTangent (lowerFamily P e he he1 i) =
      e * Real.sqrt ((P.cell i).slope^2 + 2*(P.cell i).mid^2) := by
  have hn : ‖tiltV e (P.cell i).slope (P.cell i).mid‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (tiltV_ne_zero e (P.cell i).slope (P.cell i).mid)
  have h1 : (lowerFamily P e he he1 i).axis 1 /
      (lowerFamily P e he he1 i).axis 0 = e*(P.cell i).slope := by
    change (‖tiltV e (P.cell i).slope (P.cell i).mid‖⁻¹ * (e*(P.cell i).slope)) /
      (‖tiltV e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1) = _
    field_simp
  have h2 : (lowerFamily P e he he1 i).axis 2 /
      (lowerFamily P e he he1 i).axis 0 = H*e*(P.cell i).mid := by
    change (‖tiltV e (P.cell i).slope (P.cell i).mid‖⁻¹ * (H*e*(P.cell i).mid)) /
      (‖tiltV e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1) = _
    field_simp
  rw [lowerAxisTangent, h1, h2]
  have hs : (e*(P.cell i).slope)^2 + (H*e*(P.cell i).mid)^2 =
      e^2*((P.cell i).slope^2 + 2*(P.cell i).mid^2) := by
    nlinarith only [H_sq]
  rw [hs, Real.sqrt_mul (sq_nonneg e), Real.sqrt_sq he.le]

theorem upperFamily_axisTangent (P : Partition) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (i : Fin P.count) :
    upperAxisTangent (upperFamily P e he he1 i) =
      e * Real.sqrt ((P.cell i).slope^2 + 2*(P.cell i).mid^2) := by
  have hn : ‖tiltW e (P.cell i).slope (P.cell i).mid‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (tiltW_ne_zero e (P.cell i).slope (P.cell i).mid)
  have h0 : (upperFamily P e he he1 i).axis 0 /
      (upperFamily P e he he1 i).axis 1 = -(e*(P.cell i).slope) := by
    change (‖tiltW e (P.cell i).slope (P.cell i).mid‖⁻¹ * (-e*(P.cell i).slope)) /
      (‖tiltW e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1) = _
    field_simp
  have h2 : (upperFamily P e he he1 i).axis 2 /
      (upperFamily P e he he1 i).axis 1 = H*e*(P.cell i).mid := by
    change (‖tiltW e (P.cell i).slope (P.cell i).mid‖⁻¹ * (H*e*(P.cell i).mid)) /
      (‖tiltW e (P.cell i).slope (P.cell i).mid‖⁻¹ * 1) = _
    field_simp
  rw [upperAxisTangent, h0, h2]
  have hs : (-(e*(P.cell i).slope))^2 + (H*e*(P.cell i).mid)^2 =
      e^2*((P.cell i).slope^2 + 2*(P.cell i).mid^2) := by
    nlinarith only [H_sq]
  rw [hs, Real.sqrt_mul (sq_nonneg e), Real.sqrt_sq he.le]

/-- Actual axis tangents indexed in the same lower-then-upper order as
`finiteFamily`. Each half uses its own original horizontal edge direction. -/
def familyAxisTangent (P : Partition) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    Fin (2 * P.count) → ℝ :=
  (Fin.append
    (fun i => lowerAxisTangent (lowerFamily P e he he1 i))
    (fun i => upperAxisTangent (upperFamily P e he he1 i))) ∘
      Fin.cast (two_mul P.count)

private theorem cell_speed_bound (I : Cell) :
    I.slope^2 + 2*I.mid^2 ≤ 3*(1-I.half)^2 := by
  have hc : |I.mid| ≤ 1-I.half := by linarith only [I.abs_mid_add_half]
  have hc2 := pow_le_pow_left₀ (abs_nonneg I.mid) hc 2
  rw [sq_abs] at hc2
  have hid := I.slope_mid_identity
  dsimp [G] at hid
  have hs : I.slope ≤ 1-I.half := by nlinarith only [hid, hc2]
  have hs2 := pow_le_pow_left₀ I.slope_nonneg hs 2
  nlinarith only [hs2, hc2]

private theorem uniform_half (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((uniformPartition N hN).cell i).half = 1/(N : ℝ) := by
  rw [Cell.half, uniformPartition_width]
  ring

private theorem uniform_shrink_nonneg (N : ℕ) (hN : 0 < N) :
    0 ≤ 1 - 1/(N : ℝ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  exact sub_nonneg.mpr ((div_le_one hN').mpr hN1)

private theorem uniform_speed_sqrt_le (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Real.sqrt (((uniformPartition N hN).cell i).slope^2 +
      2*((uniformPartition N hN).cell i).mid^2) ≤
      Real.sqrt 3 * (1-1/(N : ℝ)) := by
  have hs := cell_speed_bound ((uniformPartition N hN).cell i)
  rw [uniform_half] at hs
  calc
    _ ≤ Real.sqrt (3*(1-1/(N : ℝ))^2) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_sq (uniform_shrink_nonneg N hN)]

theorem uniform_axisTangent_le (N : ℕ) (hN : 0 < N) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (i : Fin (2*N)) :
    familyAxisTangent (uniformPartition N hN) e he he1 i ≤
      Real.sqrt 3 * e * (1-1/(N : ℝ)) := by
  have hl (j : Fin N) : lowerAxisTangent (lowerFamily (uniformPartition N hN) e he he1 j) ≤
      Real.sqrt 3 * e * (1-1/(N : ℝ)) := by
    rw [lowerFamily_axisTangent]
    have := mul_le_mul_of_nonneg_left (uniform_speed_sqrt_le N hN j) he.le
    nlinarith only [this]
  have hu (j : Fin N) : upperAxisTangent (upperFamily (uniformPartition N hN) e he he1 j) ≤
      Real.sqrt 3 * e * (1-1/(N : ℝ)) := by
    rw [upperFamily_axisTangent]
    have := mul_le_mul_of_nonneg_left (uniform_speed_sqrt_le N hN j) he.le
    nlinarith only [this]
  dsimp only [familyAxisTangent, Function.comp_apply]
  exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hl j)
    (fun j => by simpa only [Fin.append_right] using hu j) (Fin.cast (two_mul N) i)

/-- The uniform finite mesh attains its exact maximum axis tangent, including
the degenerate-angle case `N = 1`. The cylinder bases remain nondegenerate. -/
theorem uniform_maximum_axisTangent (N : ℕ) (hN : 0 < N) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) :
    IsGreatest (Set.range (familyAxisTangent (uniformPartition N hN) e he he1))
      (Real.sqrt 3 * e * (1-1/(N : ℝ))) := by
  constructor
  · let j : Fin N := ⟨0, hN⟩
    refine ⟨Fin.cast (two_mul N).symm (Fin.castAdd N j), ?_⟩
    simp only [familyAxisTangent, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_left]
    rw [lowerFamily_axisTangent]
    have hc : ((uniformPartition N hN).cell j).mid = -(1-1/(N : ℝ)) := by
      dsimp [uniformPartition, Partition.cell, Cell.mid, j]
      norm_num
      ring
    have ha : ((uniformPartition N hN).cell j).slope = 1-1/(N : ℝ) := by
      dsimp [uniformPartition, Partition.cell, Cell.slope, j]
      norm_num
      ring
    rw [hc, ha]
    have hid : (1-1/(N : ℝ))^2 + 2*(-(1-1/(N : ℝ)))^2 =
        3*(1-1/(N : ℝ))^2 := by ring
    rw [hid, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_sq (uniform_shrink_nonneg N hN)]
    ring
  · rintro _ ⟨i, rfl⟩
    exact uniform_axisTangent_le N hN e he he1 i

end
end TetrahedronCover
