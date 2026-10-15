import VixOverlap.Model
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
Finite conditional averages for equivalence-class histories. Division occurs
only in the positive-history-mass branch. Reconstruction and tower identities
are unnormalized and therefore also hold on histories of mass zero.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace VixOverlap.FiniteConditioning

variable {Ω : Type*} [Fintype Ω]

def conditionalAverage (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  if 0 < historyMass p.weight H ω then
    historySum p.weight H ω f / historyMass p.weight H ω
  else 0

theorem mass_eq_sum (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω) :
    historyMass p.weight H ω = ∑ η, if H.r ω η then p.weight η else 0 := by
  classical
  simp only [historyMass, historySum, mul_one]

theorem mass_nonneg (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω) :
    0 ≤ historyMass p.weight H ω := by
  classical
  rw [mass_eq_sum]
  apply Finset.sum_nonneg
  intro η _
  split_ifs
  · exact p.nonneg η
  · exact le_rfl

theorem related_sum_eq (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    {ω η : Ω} (h : H.r ω η) :
    historySum p.weight H ω f = historySum p.weight H η f := by
  classical
  unfold historySum
  apply Finset.sum_congr rfl
  intro ξ _
  have hr : H.r ω ξ ↔ H.r η ξ :=
    ⟨fun hx => H.trans (H.symm h) hx, fun hx => H.trans h hx⟩
  rw [hr]

theorem related_mass_eq (p : FiniteLaw Ω) (H : Setoid Ω)
    {ω η : Ω} (h : H.r ω η) :
    historyMass p.weight H ω = historyMass p.weight H η :=
  related_sum_eq p H (fun _ => 1) h

theorem weight_le_mass (p : FiniteLaw Ω) (H : Setoid Ω)
    {ω η : Ω} (h : H.r ω η) : p.weight η ≤ historyMass p.weight H ω := by
  classical
  rw [mass_eq_sum]
  have bound := Finset.single_le_sum
    (s := (Finset.univ : Finset Ω))
    (f := fun ξ => if H.r ω ξ then p.weight ξ else 0)
    (by
      intro ξ _
      split_ifs
      · exact p.nonneg ξ
      · exact le_rfl)
    (Finset.mem_univ η)
  simpa only [h, ite_true] using bound

theorem mass_pos_of_weight_pos (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω)
    (positive : 0 < p.weight ω) : 0 < historyMass p.weight H ω :=
  positive.trans_le (weight_le_mass p H (H.refl ω))

theorem weight_zero_of_mass_zero (p : FiniteLaw Ω) (H : Setoid Ω)
    {ω η : Ω} (zero : historyMass p.weight H ω = 0) (h : H.r ω η) :
    p.weight η = 0 :=
  le_antisymm ((weight_le_mass p H h).trans_eq zero) (p.nonneg η)

theorem sum_zero_of_mass_zero (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω)
    (zero : historyMass p.weight H ω = 0) (f : Ω → ℝ) :
    historySum p.weight H ω f = 0 := by
  classical
  unfold historySum
  apply Finset.sum_eq_zero
  intro η _
  by_cases h : H.r ω η
  · simp only [h, ite_true, weight_zero_of_mass_zero p H zero h, zero_mul]
  · simp only [h, ite_false]

theorem historySum_const (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω) (value : ℝ) :
    historySum p.weight H ω (fun _ => value) = value * historyMass p.weight H ω := by
  classical
  rw [mass_eq_sum]
  unfold historySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs <;> ring

theorem historySum_add (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω) (f g : Ω → ℝ) :
    historySum p.weight H ω (fun η => f η + g η) =
      historySum p.weight H ω f + historySum p.weight H ω g := by
  classical
  unfold historySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs <;> ring

theorem historySum_scale (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω)
    (scalar : ℝ) (f : Ω → ℝ) :
    historySum p.weight H ω (fun η => scalar * f η) =
      scalar * historySum p.weight H ω f := by
  classical
  unfold historySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs <;> ring

theorem historySum_congr (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω)
    (f g : Ω → ℝ) (equal : ∀ η, H.r ω η → f η = g η) :
    historySum p.weight H ω f = historySum p.weight H ω g := by
  classical
  unfold historySum
  apply Finset.sum_congr rfl
  intro η _
  by_cases h : H.r ω η
  · simp only [h, ite_true, equal η h]
  · simp only [h, ite_false]

theorem avg_adapted (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    {ω η : Ω} (h : H.r ω η) :
    conditionalAverage p H f ω = conditionalAverage p H f η := by
  unfold conditionalAverage
  rw [related_sum_eq p H f h, related_mass_eq p H h]

theorem avg_reconstruct (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ) (ω : Ω) :
    historySum p.weight H ω f =
      conditionalAverage p H f ω * historyMass p.weight H ω := by
  by_cases positive : 0 < historyMass p.weight H ω
  · simp only [conditionalAverage, positive, ite_true,
      div_mul_cancel₀ _ positive.ne']
  · have zero : historyMass p.weight H ω = 0 :=
      le_antisymm (not_lt.mp positive) (mass_nonneg p H ω)
    rw [sum_zero_of_mass_zero p H ω zero f]
    simp only [conditionalAverage, positive, ite_false, zero_mul]

theorem avg_eq_of_history_sum (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    (ω : Ω) (positive : 0 < historyMass p.weight H ω) (value : ℝ)
    (row : historySum p.weight H ω f = value * historyMass p.weight H ω) :
    conditionalAverage p H f ω = value := by
  rw [conditionalAverage, if_pos positive, row]
  exact mul_div_cancel_right₀ value positive.ne'

theorem avg_const_on_history (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    (ω : Ω) (positive : 0 < historyMass p.weight H ω) (value : ℝ)
    (constant : ∀ η, H.r ω η → f η = value) :
    conditionalAverage p H f ω = value := by
  apply avg_eq_of_history_sum p H f ω positive value
  rw [historySum_congr p H ω f (fun _ => value) constant, historySum_const]

theorem avg_zero (p : FiniteLaw Ω) (H : Setoid Ω) (ω : Ω) :
    conditionalAverage p H (fun _ => 0) ω = 0 := by
  unfold conditionalAverage
  rw [historySum_const]
  split_ifs <;> simp

theorem avg_add (p : FiniteLaw Ω) (H : Setoid Ω) (f g : Ω → ℝ) (ω : Ω) :
    conditionalAverage p H (fun η => f η + g η) ω =
      conditionalAverage p H f ω + conditionalAverage p H g ω := by
  unfold conditionalAverage
  rw [historySum_add]
  split_ifs <;> simp only [add_div, add_zero]

theorem avg_scale (p : FiniteLaw Ω) (H : Setoid Ω) (scalar : ℝ)
    (f : Ω → ℝ) (ω : Ω) :
    conditionalAverage p H (fun η => scalar * f η) ω =
      scalar * conditionalAverage p H f ω := by
  unfold conditionalAverage
  rw [historySum_scale]
  split_ifs <;> ring

theorem avg_finset_sum {ι : Type*} (p : FiniteLaw Ω) (H : Setoid Ω)
    (indices : Finset ι) (f : ι → Ω → ℝ) (ω : Ω) :
    conditionalAverage p H (fun η => ∑ i ∈ indices, f i η) ω =
      ∑ i ∈ indices, conditionalAverage p H (f i) ω := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, avg_zero]
  | @insert i indices absent ih =>
      simp only [Finset.sum_insert absent, avg_add, ih]

theorem avg_nonneg (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    (nonnegative : ∀ η, 0 ≤ f η) (ω : Ω) :
    0 ≤ conditionalAverage p H f ω := by
  classical
  unfold conditionalAverage
  split_ifs with positive
  · apply div_nonneg _ positive.le
    unfold historySum
    apply Finset.sum_nonneg
    intro η _
    split_ifs
    · exact mul_nonneg (p.nonneg η) (nonnegative η)
    · exact le_rfl
  · exact le_rfl

theorem avg_le (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound) (bounded : ∀ η, f η ≤ bound) (ω : Ω) :
    conditionalAverage p H f ω ≤ bound := by
  classical
  unfold conditionalAverage
  split_ifs with positive
  · apply (div_le_iff₀ positive).mpr
    rw [← historySum_const p H ω bound]
    unfold historySum
    apply Finset.sum_le_sum
    intro η _
    split_ifs
    · exact mul_le_mul_of_nonneg_left (bounded η) (p.nonneg η)
    · exact le_rfl
  · exact bound_nonneg

theorem historySum_avg_same (p : FiniteLaw Ω) (H : Setoid Ω) (f : Ω → ℝ) (ω : Ω) :
    historySum p.weight H ω (conditionalAverage p H f) = historySum p.weight H ω f := by
  rw [historySum_congr p H ω (conditionalAverage p H f)
    (fun _ => conditionalAverage p H f ω)
    (fun η related => (avg_adapted p H f related).symm)]
  rw [historySum_const, ← avg_reconstruct]

/-- Equal integrals on every fine history give equal integrals on every coarse
history. The proof partitions the finite state sum into equivalence classes. -/
theorem historySum_eq_of_refines (p : FiniteLaw Ω) (coarse fine : Setoid Ω)
    (refines : ∀ ω η, fine.r ω η → coarse.r ω η) (f g : Ω → ℝ)
    (local_equal : ∀ η, historySum p.weight fine η f = historySum p.weight fine η g)
    (ω : Ω) : historySum p.weight coarse ω f = historySum p.weight coarse ω g := by
  classical
  have regroup (u : Ω → ℝ) : historySum p.weight coarse ω u =
      ∑ q : Quotient fine,
        if coarse.r ω q.out then historySum p.weight fine q.out u else 0 := by
    have grouping := Finset.sum_fiberwise (Finset.univ : Finset Ω)
      (Quotient.mk fine) (fun η => if coarse.r ω η then p.weight η * u η else 0)
    unfold historySum
    rw [← grouping]
    apply Finset.sum_congr rfl
    intro q _
    have fiber (η : Ω) : Quotient.mk fine η = q ↔ fine.r q.out η := by
      constructor
      · intro equal
        apply Quotient.exact
        exact (Quotient.out_eq q).trans equal.symm
      · intro related
        exact (Quotient.sound (fine.symm related)).trans (Quotient.out_eq q)
    rw [Finset.sum_filter]
    by_cases hc : coarse.r ω q.out
    · simp only [hc, ite_true]
      apply Finset.sum_congr rfl
      intro η _
      by_cases hf : fine.r q.out η
      · have hη : coarse.r ω η := coarse.trans hc (refines _ _ hf)
        simp only [fiber, hf, hη, ite_true]
      · simp only [fiber, hf, ite_false]
    · simp only [hc, ite_false]
      apply Finset.sum_eq_zero
      intro η _
      by_cases hf : fine.r q.out η
      · have hη : ¬ coarse.r ω η := fun related =>
          hc (coarse.trans related (coarse.symm (refines _ _ hf)))
        simp only [fiber, hf, hη, ite_true, ite_false]
      · simp only [fiber, hf, ite_false]
  rw [regroup f, regroup g]
  apply Finset.sum_congr rfl
  intro q _
  rw [local_equal]

theorem avg_tower_hsum (p : FiniteLaw Ω) (coarse fine : Setoid Ω)
    (refines : ∀ ω η, fine.r ω η → coarse.r ω η) (f : Ω → ℝ) (ω : Ω) :
    historySum p.weight coarse ω (conditionalAverage p fine f) =
      conditionalAverage p coarse f ω * historyMass p.weight coarse ω := by
  rw [historySum_eq_of_refines p coarse fine refines (conditionalAverage p fine f) f
    (historySum_avg_same p fine f)]
  exact avg_reconstruct p coarse f ω

theorem avg_tower (p : FiniteLaw Ω) (coarse fine : Setoid Ω)
    (refines : ∀ ω η, fine.r ω η → coarse.r ω η) (f : Ω → ℝ) (ω : Ω) :
    conditionalAverage p coarse (conditionalAverage p fine f) ω =
      conditionalAverage p coarse f ω := by
  have equal := historySum_eq_of_refines p coarse fine refines
    (conditionalAverage p fine f) f (historySum_avg_same p fine f) ω
  change (if 0 < historyMass p.weight coarse ω then
      historySum p.weight coarse ω (conditionalAverage p fine f) /
        historyMass p.weight coarse ω else 0) =
    (if 0 < historyMass p.weight coarse ω then
      historySum p.weight coarse ω f / historyMass p.weight coarse ω else 0)
  rw [equal]

theorem mass_root (p : FiniteLaw Ω) (H : Setoid Ω)
    (root : ∀ ω η, H.r ω η) (ω : Ω) : historyMass p.weight H ω = 1 := by
  classical
  simpa only [mass_eq_sum, root, ite_true] using p.total

theorem avg_root (p : FiniteLaw Ω) (H : Setoid Ω)
    (root : ∀ ω η, H.r ω η) (f : Ω → ℝ) (ω : Ω) :
    conditionalAverage p H f ω = ∑ η, p.weight η * f η := by
  classical
  simp only [conditionalAverage, mass_root p H root ω, zero_lt_one, ite_true,
    div_one, historySum, root]

end VixOverlap.FiniteConditioning
