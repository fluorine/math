module

public import TetrahedronCover.Algebra
public import TetrahedronCover.Partition
public import TetrahedronCover.BenchmarkPolynomials
public import Mathlib.Data.Fin.Rev
public import Mathlib.Algebra.BigOperators.Fin

/-!
The numerical certificate is about the actual 10,000-cell secant construction.
This file identifies its caps and square-root denominators, proves the
reflection pairing of all 10,000 cells, and transfers the checked rational
polynomial sums to the true area sum.  Thus the polynomial calculation is not
an unconnected auxiliary number.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section
open scoped BigOperators

/-- The actual equally spaced partition used by the 20,000-cylinder example. -/
def benchmarkPartition : Partition := uniformPartition 10000 (by norm_num)

/-- One of the 10,000 angular cells; each produces a lower and an upper cylinder. -/
def benchmarkCell (i : Fin 10000) : Cell := benchmarkPartition.cell i

/-- The normalized area sum, including both cylinders from every cell. -/
def benchmarkCost : ℝ := ∑ i : Fin 10000, (benchmarkCell i).term (1/10)

lemma benchmark_cell_left (i : Fin 10000) :
    (benchmarkCell i).left = -1+(i : ℝ)/5000 := by
  dsimp [benchmarkCell, benchmarkPartition, uniformPartition, Partition.cell]
  ring

lemma benchmark_cell_right (i : Fin 10000) :
    (benchmarkCell i).right = -1+((i : ℝ)+1)/5000 := by
  dsimp [benchmarkCell, benchmarkPartition, uniformPartition, Partition.cell]
  push_cast
  ring

lemma benchmark_cell_width (i : Fin 10000) :
    (benchmarkCell i).width = 1/5000 := by
  unfold Cell.width
  rw [benchmark_cell_left, benchmark_cell_right]
  ring

lemma benchmark_positive_left (j : Fin 5000) :
    (benchmarkCell (Fin.natAdd 5000 j)).left = (j : ℝ)/5000 := by
  rw [benchmark_cell_left]
  simp only [Fin.val_natAdd, Nat.cast_add]
  norm_num
  ring

lemma benchmark_positive_right (j : Fin 5000) :
    (benchmarkCell (Fin.natAdd 5000 j)).right = ((j : ℝ)+1)/5000 := by
  rw [benchmark_cell_right]
  simp only [Fin.val_natAdd, Nat.cast_add]
  norm_num
  ring

lemma benchmark_cell_padding (i : Fin 10000) :
    (benchmarkCell i).padding (1/10) = benchmarkDelta := by
  unfold Cell.padding Cell.half
  rw [benchmark_cell_width]
  norm_num [K₀, Mstar, benchmarkDelta]

/-- A nonnegative cell attains its largest cap at its right endpoint. -/
lemma Cell.cap_eq_right {I : Cell} (e : ℝ) (hl : 0 ≤ I.left) :
    I.cap e = C e I.right+I.padding e := by
  have hs : I.left^2 ≤ I.right^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr I.strict.le)
      (show 0 ≤ I.right+I.left by linarith [I.strict])]
  unfold Cell.cap
  rw [max_eq_right (C_le_C_of_sq_le (e := e) hs)]

lemma benchmark_positive_cap (j : Fin 5000) :
    (benchmarkCell (Fin.natAdd 5000 j)).cap (1/10) = benchmarkCap (j : ℝ) := by
  rw [Cell.cap_eq_right]
  · rw [benchmark_positive_right, benchmark_cell_padding]
    rfl
  · rw [benchmark_positive_left]
    positivity

lemma benchmark_positive_argument (j : Fin 5000) :
    (1/10 : ℝ)^2 * ((benchmarkCell (Fin.natAdd 5000 j)).slope^2+
      2*(benchmarkCell (Fin.natAdd 5000 j)).mid^2) = benchmarkArgument (j : ℝ) := by
  unfold Cell.slope Cell.mid
  rw [benchmark_positive_left, benchmark_positive_right]
  unfold benchmarkArgument
  ring

lemma benchmark_argument_bounds (j : Fin 5000) :
    0 ≤ benchmarkArgument (j : ℝ) ∧ benchmarkArgument (j : ℝ) ≤ 1 := by
  rw [← benchmark_positive_argument j]
  let I := benchmarkCell (Fin.natAdd 5000 j)
  have hs0 := I.slope_nonneg
  have hs1 := I.slope_le_one
  have hs2 : I.slope^2 ≤ 1 := by nlinarith
  have hm2 := sq_le_one I.mid_abs_le
  constructor
  · positivity
  · change (1/10 : ℝ)^2*(I.slope^2+2*I.mid^2) ≤ 1
    nlinarith only [hs2, hm2]

lemma C_neg (e q : ℝ) : C e (-q) = C e q := by
  unfold C h G
  ring

/-- Reflecting the angular cell preserves its actual secant area term. -/
lemma Cell.term_reflection {I J : Cell} (e : ℝ)
    (hl : J.left = -I.right) (hr : J.right = -I.left) : J.term e = I.term e := by
  have hw : J.width = I.width := by unfold Cell.width; rw [hl, hr]; ring
  have ha : J.half = I.half := by unfold Cell.half; rw [hw]
  have hc : J.mid = -I.mid := by unfold Cell.mid; rw [hl, hr]; ring
  have hA : J.slope = I.slope := by unfold Cell.slope; rw [hl, hr]; ring
  have hp : J.padding e = I.padding e := by unfold Cell.padding; rw [ha]
  have hM : J.cap e = I.cap e := by
    unfold Cell.cap
    rw [hl, hr, C_neg, C_neg, hp, max_comm]
  unfold Cell.term
  rw [hw, hc, hA, hM, neg_sq]

lemma benchmark_reflected_pair (j : Fin 5000) :
    (benchmarkCell (Fin.castAdd 5000 j)).term (1/10) =
      (benchmarkCell (Fin.natAdd 5000 j.rev)).term (1/10) := by
  have hrev : (j.rev : ℝ)+(j : ℝ) = 4999 := by
    exact_mod_cast (Fin.rev_add_cast j)
  apply Cell.term_reflection
  · rw [benchmark_cell_left, benchmark_positive_right]
    change -1+(j : ℝ)/5000 = -(((j.rev : ℝ)+1)/5000)
    linarith only [hrev]
  · rw [benchmark_cell_right, benchmark_positive_left]
    change -1+((j : ℝ)+1)/5000 = -((j.rev : ℝ)/5000)
    linarith only [hrev]

/-- All 10,000 cells are accounted for; none are discarded by symmetry. -/
theorem benchmark_paired_sum : benchmarkCost =
    ∑ j : Fin 5000, 2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10) := by
  unfold benchmarkCost
  change (∑ i : Fin (5000+5000), (benchmarkCell i).term (1/10)) = _
  rw [Fin.sum_univ_add]
  have hleft : (∑ j : Fin 5000, (benchmarkCell (Fin.castAdd 5000 j)).term (1/10)) =
      ∑ j : Fin 5000, (benchmarkCell (Fin.natAdd 5000 j)).term (1/10) := by
    calc
      _ = ∑ j : Fin 5000, (benchmarkCell (Fin.natAdd 5000 j.rev)).term (1/10) := by
        apply Finset.sum_congr rfl
        intro j _
        exact benchmark_reflected_pair j
      _ = _ := Equiv.sum_comp Fin.revPerm
        (fun j : Fin 5000 => (benchmarkCell (Fin.natAdd 5000 j)).term (1/10))
  rw [hleft]
  simp only [two_mul, Finset.sum_add_distrib]

lemma benchmark_positive_term (j : Fin 5000) :
    2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10) =
      (benchmarkCap (j : ℝ))^2 * (1/Real.sqrt (1+benchmarkArgument (j : ℝ))) / 10000 := by
  unfold Cell.term
  rw [benchmark_cell_width, benchmark_positive_cap, benchmark_positive_argument]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The analytic square-root term is enclosed by the two checked polynomials. -/
lemma benchmark_term_bounds (j : Fin 5000) :
    benchmarkSummand9 (j : ℝ) ≤
      2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10) ∧
    2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10) ≤
      benchmarkSummand8 (j : ℝ) := by
  obtain ⟨hz, hz1⟩ := benchmark_argument_bounds j
  obtain ⟨hl, hu⟩ := inverse_sqrt_bounds hz hz1
  rw [benchmark_positive_term]
  constructor
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (sq_nonneg (benchmarkCap (j : ℝ)))) (by norm_num)
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (sq_nonneg (benchmarkCap (j : ℝ)))) (by norm_num)

/-- Exact rational interval for the actual 20,000-cylinder normalized area. -/
theorem benchmark_interval :
    (499921585997001674 / 1000000000000000000 : ℝ) ≤ benchmarkCost ∧
    benchmarkCost ≤ (499921585997001774 / 1000000000000000000 : ℝ) := by
  have hl : (∑ j : Fin 5000, benchmarkSummand9 (j : ℝ)) ≤
      ∑ j : Fin 5000, 2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10) :=
    Finset.sum_le_sum (fun j _ => (benchmark_term_bounds j).1)
  have hu : (∑ j : Fin 5000, 2*(benchmarkCell (Fin.natAdd 5000 j)).term (1/10)) ≤
      ∑ j : Fin 5000, benchmarkSummand8 (j : ℝ) :=
    Finset.sum_le_sum (fun j _ => (benchmark_term_bounds j).2)
  have hlo : (499921585997001674 / 1000000000000000000 : ℝ) ≤
      ∑ j : Fin 5000, benchmarkSummand9 (j : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => benchmarkSummand9 (k : ℝ)) 5000]
    exact benchmark_lower_rational
  have hup : (∑ j : Fin 5000, benchmarkSummand8 (j : ℝ)) ≤
      (499921585997001774 / 1000000000000000000 : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => benchmarkSummand8 (k : ℝ)) 5000]
    exact benchmark_upper_rational
  rw [benchmark_paired_sum]
  exact ⟨hlo.trans hl, hu.trans hup⟩

/-- The advertised strict improvement follows from the verified interval. -/
theorem benchmark_strict : benchmarkCost < (499922/1000000 : ℝ) := by
  have h := benchmark_interval.2
  linarith

end
end TetrahedronCover
