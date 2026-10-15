import VixOverlap.Payoff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite positive-support call identification. This file contains no financial
realization assumption: it is the ordinary vanilla-payoff bridge. -/

noncomputable section
open scoped BigOperators

namespace VixOverlap.Vanilla

def callSum {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ) (K : ℝ) : ℝ :=
  ∑ ω, p ω * callPayoff K (X ω)

def massAt {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ ω, if X ω = x then p ω else 0

private theorem finite_gap (s : Finset ℝ) (x : ℝ) (hx : 0 < x) :
    ∃ d : ℝ, 0 < d ∧ d ≤ x ∧ ∀ y ∈ s, y = x ∨ d ≤ |y - x| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨x, hx, le_rfl, by simp⟩
  | @insert y s hy ih =>
    obtain ⟨d, hd, hdx, hds⟩ := ih
    by_cases h : y = x
    · refine ⟨d, hd, hdx, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inl h
      · exact hds z hz
    · refine ⟨min d |y - x|, lt_min hd (abs_pos.mpr (sub_ne_zero.mpr h)),
        (min_le_left _ _).trans hdx, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inr (min_le_right _ _)
      · rcases hds z hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr ((min_le_left _ _).trans hz)

private theorem tent_value (x y d : ℝ) (hd : 0 < d)
    (hgap : y = x ∨ d ≤ |y - x|) :
    callPayoff (x-d) y - 2 * callPayoff x y + callPayoff (x+d) y =
      if y = x then d else 0 := by
  classical
  by_cases h : y = x
  · subst y
    simp [callPayoff, max_eq_left hd.le, max_eq_right (neg_nonpos.mpr hd.le)]
  · rw [if_neg h]
    have hg := hgap.resolve_left h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [abs_of_neg (sub_neg.mpr hlt)] at hg
      have h1 : y - (x-d) ≤ 0 := by linarith
      have h2 : y-x ≤ 0 := by linarith
      have h3 : y-(x+d) ≤ 0 := by linarith
      simp [callPayoff, max_eq_right h1, max_eq_right h2, max_eq_right h3]
    · rw [abs_of_pos (sub_pos.mpr hgt)] at hg
      have h1 : 0 ≤ y-(x-d) := by linarith
      have h2 : 0 ≤ y-x := by linarith
      have h3 : 0 ≤ y-(x+d) := by linarith
      simp only [callPayoff, max_eq_left h1, max_eq_left h2, max_eq_left h3]
      ring

private theorem tent_sum {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
    (x d : ℝ) (hd : 0 < d) (hgap : ∀ ω, X ω = x ∨ d ≤ |X ω-x|) :
    callSum p X (x-d) - 2 * callSum p X x + callSum p X (x+d) =
      d * massAt p X x := by
  classical
  calc
    _ = ∑ ω, p ω * (callPayoff (x-d) (X ω) -
        2 * callPayoff x (X ω) + callPayoff (x+d) (X ω)) := by
      simp only [callSum, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = ∑ ω, d * (if X ω = x then p ω else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [tent_value x (X ω) d hd (hgap ω)]
      split_ifs <;> ring
    _ = _ := by simp only [massAt, Finset.mul_sum]

/-- Equality of all ordinary nonnegative-strike calls identifies every atom of
two finite positive-supported laws. Weights may even be signed; no hidden
probability or support-identification assumption is used. -/
theorem calls_identify_atoms {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p X : Ω → ℝ) (q Y : Ξ → ℝ)
    (hX : ∀ ω, 0 < X ω) (hY : ∀ η, 0 < Y η)
    (hc : ∀ K : ℝ, 0 ≤ K → callSum p X K = callSum q Y K) :
    ∀ x, massAt p X x = massAt q Y x := by
  classical
  intro x
  by_cases hx : 0 < x
  · let s := Finset.univ.image X ∪ Finset.univ.image Y
    obtain ⟨d, hd, hdx, hg⟩ := finite_gap s x hx
    have gx : ∀ ω, X ω = x ∨ d ≤ |X ω-x| := by
      intro ω
      exact hg _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩))
    have gy : ∀ η, Y η = x ∨ d ≤ |Y η-x| := by
      intro η
      exact hg _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨η, Finset.mem_univ _, rfl⟩))
    have hp := tent_sum p X x d hd gx
    have hq := tent_sum q Y x d hd gy
    rw [hc (x-d) (sub_nonneg.mpr hdx), hc x hx.le,
      hc (x+d) (by linarith)] at hp
    exact mul_left_cancel₀ (ne_of_gt hd) (hp.symm.trans hq)
  · have hxp : ∀ ω, X ω ≠ x := by intro ω h; have := hX ω; rw [h] at this; exact hx this
    have hyp : ∀ η, Y η ≠ x := by intro η h; have := hY η; rw [h] at this; exact hx this
    simp [massAt, hxp, hyp]

private theorem sum_by_atoms {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
    (f : ℝ → ℝ) (s : Finset ℝ) (hs : ∀ ω, X ω ∈ s) :
    (∑ x ∈ s, massAt p X x * f x) = ∑ ω, p ω * f (X ω) := by
  classical
  simp only [massAt, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp_rw [ite_mul, zero_mul]
  simp [eq_comm, hs ω]

/-- Ordinary call equality preserves every function of the finite stock value. -/
theorem calls_identify_expectations {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p X : Ω → ℝ) (q Y : Ξ → ℝ)
    (hX : ∀ ω, 0 < X ω) (hY : ∀ η, 0 < Y η)
    (hc : ∀ K : ℝ, 0 ≤ K → callSum p X K = callSum q Y K)
    (f : ℝ → ℝ) :
    (∑ ω, p ω * f (X ω)) = ∑ η, q η * f (Y η) := by
  classical
  let s := Finset.univ.image X ∪ Finset.univ.image Y
  have hx : ∀ ω, X ω ∈ s := by
    intro ω
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩)
  have hy : ∀ η, Y η ∈ s := by
    intro η
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨η, Finset.mem_univ _, rfl⟩)
  rw [← sum_by_atoms p X f s hx, ← sum_by_atoms q Y f s hy]
  apply Finset.sum_congr rfl
  intro x _
  rw [calls_identify_atoms p X q Y hX hY hc x]

/-- A latent statistic may be recovered from calls only after proving that it
is constant on each price fiber. This is the support-identification obligation,
not an assumption that the statistic itself is an observed instrument. -/
theorem calls_identify_fiber_statistic {Ω : Type*} [Fintype Ω]
    (p q X f : Ω → ℝ) (hX : ∀ ω, 0 < X ω)
    (hf : ∀ ω η, X ω = X η → f ω = f η)
    (hc : ∀ K : ℝ, 0 ≤ K → callSum p X K = callSum q X K) :
    (∑ ω, p ω * f ω) = ∑ ω, q ω * f ω := by
  classical
  let g : ℝ → ℝ := fun x => if h : ∃ ω, X ω = x then f (Classical.choose h) else 0
  have hg : ∀ ω, g (X ω) = f ω := by
    intro ω
    have h : ∃ η, X η = X ω := ⟨ω, rfl⟩
    simp only [g, dif_pos h]
    exact hf _ _ (Classical.choose_spec h)
  have he := calls_identify_expectations p X q X hX hX hc g
  simpa only [hg] using he

/-- The zero atom is recovered using the common cash price (total mass).
This version applies to VIX, which may vanish. -/
theorem nonneg_calls_identify_fiber_statistic {Ω : Type*} [Fintype Ω]
    (p q X f : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (htotal : (∑ ω, p ω) = ∑ ω, q ω)
    (hf : ∀ ω η, X ω = X η → f ω = f η)
    (hc : ∀ K : ℝ, 0 ≤ K → callSum p X K = callSum q X K) :
    (∑ ω, p ω * f ω) = ∑ ω, q ω * f ω := by
  classical
  have hm : (∑ ω, p ω * X ω) = ∑ ω, q ω * X ω := by
    simpa [callSum, callPayoff, max_eq_left (hX _)] using hc 0 (by rfl)
  apply calls_identify_fiber_statistic p q (fun ω => X ω+1) f
  · intro ω; linarith [hX ω]
  · intro ω η h
    exact hf ω η (by linarith)
  · intro K hK
    by_cases hk : 1 ≤ K
    · have hpoint : ∀ ω, callPayoff K (X ω+1) = callPayoff (K-1) (X ω) := by
        intro ω; unfold callPayoff; congr 1 <;> ring
      simpa only [callSum, hpoint] using hc (K-1) (sub_nonneg.mpr hk)
    · have hpoint : ∀ ω, callPayoff K (X ω+1) = X ω+(1-K) := by
        intro ω
        rw [callPayoff, max_eq_left (by linarith [hX ω])]
        ring
      simp only [callSum, hpoint, mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, hm, htotal]

/-- Exact finite grouping by a statistic. -/
theorem sum_by_statistic {Ω T : Type*} [Fintype Ω] [Fintype T]
    [DecidableEq T]
    (p : Ω → ℝ) (X : Ω → T) (f : T → ℝ) :
    (∑ ω, p ω * f (X ω)) =
      ∑ t, f t * ∑ ω, if X ω = t then p ω else 0 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [mul_ite, mul_comm]

theorem masses_identify_fiber_statistic {Ω T : Type*} [Fintype Ω] [Fintype T]
    [DecidableEq T]
    (p q : Ω → ℝ) (X : Ω → T) (f : Ω → ℝ)
    (hf : ∀ ω η, X ω = X η → f ω = f η)
    (hm : ∀ t, (∑ ω, if X ω = t then p ω else 0) =
      ∑ ω, if X ω = t then q ω else 0) :
    (∑ ω, p ω * f ω) = ∑ ω, q ω * f ω := by
  classical
  let g : T → ℝ := fun t => if h : ∃ ω, X ω = t then f (Classical.choose h) else 0
  have hg : ∀ ω, g (X ω) = f ω := by
    intro ω
    have h : ∃ η, X η = X ω := ⟨ω, rfl⟩
    simp only [g, dif_pos h]
    exact hf _ _ (Classical.choose_spec h)
  have he : (∑ ω, p ω * g (X ω)) = ∑ ω, q ω * g (X ω) := by
    rw [sum_by_statistic p X g, sum_by_statistic q X g]
    apply Finset.sum_congr rfl
    intro t _
    rw [hm]
  simpa only [hg] using he

end VixOverlap.Vanilla
