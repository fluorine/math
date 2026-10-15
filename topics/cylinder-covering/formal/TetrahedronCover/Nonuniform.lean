module

public import TetrahedronCover.Continuum
public import TetrahedronCover.Partition
public import Mathlib.Data.Finset.Lattice.Fold

/-!
The quantitative finite error for every positive partition of [-1,1].
Only its maximum cell width matters; no equal spacing, shape regularity, or
bound on ratios of neighboring widths is assumed.  The same explicit error
budget as for the uniform mesh bounds the two-sided error.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section
open scoped BigOperators

/-- Enlarging a cell's width can only enlarge its explicit padding. -/
theorem uniformPadding_mono_width {e d D : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hd0 : 0 ≤ d) (hdD : d ≤ D) : uniformPadding e d ≤ uniformPadding e D := by
  have hD0 : 0 ≤ D := hd0.trans hdD
  have hs : d^2 ≤ D^2 := by
    nlinarith only [mul_le_mul hdD hdD hd0 hD0]
  have hlinear := mul_le_mul_of_nonneg_left hdD (K₀_nonneg he0)
  have hquadratic := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Mstar e*e^2/4 by have := Mstar_pos e; positivity)
  unfold uniformPadding
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 2*(1-e))
  unfold K₀ at hlinear
  nlinarith only [hlinear, hquadratic]

lemma Cell.padding_le_mesh (I : Cell) {e D : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hwidth : I.width ≤ D) : I.padding e ≤ uniformPadding e D := by
  rw [I.padding_eq_uniform]
  exact uniformPadding_mono_width he0 he1 (sub_nonneg.mpr I.strict.le) hwidth

/-- The widths telescope to the full angular interval's length. -/
theorem Partition.sum_width (P : Partition) : (∑ i, (P.cell i).width) = 2 := by
  change (∑ i : Fin P.count, (P.node (i+1)-P.node i)) = 2
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => P.node (k+1)-P.node k) P.count,
    Finset.sum_range_sub, P.first, P.last]
  norm_num

/-- The second width moment needs only an upper mesh bound. -/
theorem Partition.width_square_sum_le (P : Partition) {D : ℝ}
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    (∑ i, (P.cell i).width^2) ≤ 2*D := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P.count))) =>
    show (P.cell i).width^2 ≤ D*(P.cell i).width by
      have hh := mul_le_mul_of_nonneg_right (hwidth i)
        (show 0 ≤ (P.cell i).width from sub_nonneg.mpr (P.cell i).strict.le)
      nlinarith only [hh])
  rw [← Finset.mul_sum, P.sum_width] at hs
  nlinarith only [hs]

/-- The third width moment also requires no regularity of the mesh. -/
theorem Partition.width_cube_sum_le (P : Partition) {D : ℝ} (hD0 : 0 ≤ D)
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    (∑ i, (P.cell i).width^3) ≤ 2*D^2 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P.count))) =>
    show (P.cell i).width^3 ≤ D^2*(P.cell i).width by
      have hw0 : 0 ≤ (P.cell i).width := sub_nonneg.mpr (P.cell i).strict.le
      have hw2 : (P.cell i).width^2 ≤ D^2 := by
        nlinarith only [mul_le_mul (hwidth i) (hwidth i) hw0 hD0]
      have hh := mul_le_mul_of_nonneg_right hw2 hw0
      nlinarith only [hh])
  rw [← Finset.mul_sum, P.sum_width] at hs
  nlinarith only [hs]

private theorem Cell.upper_mesh_bound (I : Cell) {e D : ℝ}
    (he0 : 0 ≤ e) (he1 : e < 1) (hD0 : 0 ≤ D) (hwidth : I.width ≤ D) :
    I.term e-I.integralCost e ≤
      I.width*((2*Mstar e*uniformPadding e D+(uniformPadding e D)^2)/4 +
        (Mstar e)^2*e^2*D^2/32+3*(Mstar e)^2*e^2*D/16) +
      (Mstar e*e^2*D/2)*(capVariation I.right-capVariation I.left) := by
  have hw0 : 0 ≤ I.width := sub_nonneg.mpr I.strict.le
  have hM0 := (Mstar_pos e).le
  have hp0 := I.padding_nonneg he0 he1
  have hP0 := uniformPadding_nonneg he0 he1 hD0
  have hp := I.padding_le_mesh he0 he1 hwidth
  have hpsq : (I.padding e)^2 ≤ (uniformPadding e D)^2 := by
    nlinarith only [mul_le_mul hp hp hp0 hP0]
  have hpm := mul_le_mul_of_nonneg_left hp hM0
  have hpcoef : 2*Mstar e*I.padding e+(I.padding e)^2 ≤
      2*Mstar e*uniformPadding e D+(uniformPadding e D)^2 := by
    nlinarith only [hpsq, hpm]
  have hpad := mul_le_mul_of_nonneg_left hpcoef hw0
  have hw2 : I.width^2 ≤ D*I.width := by
    nlinarith only [mul_le_mul_of_nonneg_right hwidth hw0]
  have hw2D : I.width^2 ≤ D^2 := by
    nlinarith only [mul_le_mul hwidth hwidth hw0 hD0]
  have hw3 : I.width^3 ≤ D^2*I.width := by
    nlinarith only [mul_le_mul_of_nonneg_right hw2D hw0]
  have h2 := mul_le_mul_of_nonneg_left hw2
    (show 0 ≤ (Mstar e)^2*e^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hw3
    (show 0 ≤ (Mstar e)^2*e^2 by positivity)
  have hv0 : 0 ≤ capVariation I.right-capVariation I.left :=
    sub_nonneg.mpr (capVariation_monotone I.strict.le)
  have hv := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hwidth hv0)
    (show 0 ≤ Mstar e*e^2 by positivity)
  have hcell := I.integrated_error_upper he0 he1
  nlinarith only [hpad, h2, h3, hv, hcell]

/-- The manuscript's explicit upper error budget holds for arbitrary cells. -/
theorem nonuniform_cost_upper (P : Partition) {e D : ℝ}
    (he0 : 0 ≤ e) (he1 : e < 1) (hD0 : 0 ≤ D)
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    partitionCost P e ≤ J e+finiteErrorBudget e D := by
  let U := (2*Mstar e*uniformPadding e D+(uniformPadding e D)^2)/4 +
    (Mstar e)^2*e^2*D^2/32+3*(Mstar e)^2*e^2*D/16
  let V := Mstar e*e^2*D/2
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P.count))) =>
    (P.cell i).upper_mesh_bound he0 he1 hD0 (hwidth i))
  change (∑ i, ((P.cell i).term e-(P.cell i).integralCost e)) ≤
    ∑ i, ((P.cell i).width*U+V*(capVariation (P.cell i).right-capVariation (P.cell i).left)) at hs
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at hs
  have hvariation := P.sum_capVariation
  simp only [Finset.sum_sub_distrib] at hvariation
  rw [P.sum_integralCost e, P.sum_width, hvariation] at hs
  have hid : 2*U+V*2 = finiteErrorBudget e D := by
    dsimp [U, V, finiteErrorBudget]
    ring
  rw [hid] at hs
  change partitionCost P e-J e ≤ finiteErrorBudget e D at hs
  linarith only [hs]

/-- The lower error is bounded by the second width moment; padding helps it. -/
theorem nonuniform_cost_lower (P : Partition) {e D : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) (_hD0 : 0 ≤ D)
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    J e-(3/8:ℝ)*(Mstar e)^2*e^2*D ≤ partitionCost P e := by
  have he_lt : e < 1 := by linarith
  obtain ⟨he2, _, _, _⟩ := small_parameter_powers he0 he1
  have hfactor : 0 ≤ 1-3*e^2/2 := by linarith only [he2]
  have hcell (i : Fin P.count) :
      (P.cell i).integralCost e-(P.cell i).term e ≤
        (3*(Mstar e)^2*e^2*D/16)*(P.cell i).width := by
    have hw0 : 0 ≤ (P.cell i).width := sub_nonneg.mpr (P.cell i).strict.le
    have hp0 := (P.cell i).padding_nonneg he0 he_lt
    have hpad : 0 ≤ (P.cell i).width*(P.cell i).padding e*(1-3*e^2/2)/2 := by
      positivity
    have hwidth2 : (P.cell i).width^2 ≤ D*(P.cell i).width := by
      nlinarith only [mul_le_mul_of_nonneg_right (hwidth i) hw0]
    have hscaled := mul_le_mul_of_nonneg_left hwidth2
      (show 0 ≤ 3*(Mstar e)^2*e^2/16 by positivity)
    have hl := (P.cell i).integrated_error_lower he0 he_lt
    nlinarith only [hpad, hscaled, hl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P.count))) => hcell i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [P.sum_integralCost e, P.sum_width] at hs
  change J e-partitionCost P e ≤ (3*(Mstar e)^2*e^2*D/16)*2 at hs
  nlinarith only [hs]

/-- A two-sided nonuniform error using the same four-term explicit budget. -/
theorem nonuniform_error_budget (P : Partition) {e D : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) (hD0 : 0 ≤ D)
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    |partitionCost P e-J e| ≤ finiteErrorBudget e D := by
  have hu := nonuniform_cost_upper P he0 (by linarith) hD0 hwidth
  have hl := nonuniform_cost_lower P he0 he1 hD0 hwidth
  have hp0 := uniformPadding_nonneg he0 (by linarith) hD0
  have hM0 := (Mstar_pos e).le
  have hnonneg : 0 ≤ Mstar e*e^2*D+Mstar e*uniformPadding e D+
      (uniformPadding e D)^2/2+(Mstar e)^2*e^2*D^2/16 := by positivity
  have hb : (3/8:ℝ)*(Mstar e)^2*e^2*D ≤ finiteErrorBudget e D := by
    unfold finiteErrorBudget
    nlinarith only [hnonneg]
  rw [abs_le]
  constructor <;> linarith only [hu, hl, hb]

/-- Any width bound in [0,2] gives the claimed effective nonuniform error. -/
theorem nonuniform_error (P : Partition) {e D : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) (hD0 : 0 ≤ D) (hD2 : D ≤ 2)
    (hwidth : ∀ i, (P.cell i).width ≤ D) :
    |partitionCost P e-J e| ≤ e*D :=
  (nonuniform_error_budget P he0 he1 hD0 hwidth).trans
    (finiteErrorBudget_le he0 he1 hD0 hD2)

/-- The largest actual cell width of a positive finite partition. -/
def Partition.mesh (P : Partition) : ℝ :=
  (Finset.univ : Finset (Fin P.count)).sup'
    ⟨⟨0, P.positive⟩, Finset.mem_univ _⟩ (fun i => (P.cell i).width)

lemma Partition.width_le_mesh (P : Partition) (i : Fin P.count) :
    (P.cell i).width ≤ P.mesh := by
  exact Finset.le_sup' (fun i => (P.cell i).width) (Finset.mem_univ i)

lemma Partition.mesh_pos (P : Partition) : 0 < P.mesh := by
  have hw : 0 < (P.cell ⟨0, P.positive⟩).width :=
    sub_pos.mpr (P.cell ⟨0, P.positive⟩).strict
  exact hw.trans_le (P.width_le_mesh ⟨0, P.positive⟩)

lemma Partition.mesh_le_two (P : Partition) : P.mesh ≤ 2 := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i _
  unfold Cell.width
  linarith [(P.cell i).left_ge, (P.cell i).right_le]

/-- Maximum-mesh form of the manuscript's arbitrary-partition theorem. -/
theorem nonuniform_mesh_error (P : Partition) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    |partitionCost P e-J e| ≤ e*P.mesh :=
  nonuniform_error P he0 he1 P.mesh_pos.le P.mesh_le_two P.width_le_mesh

end
end TetrahedronCover
