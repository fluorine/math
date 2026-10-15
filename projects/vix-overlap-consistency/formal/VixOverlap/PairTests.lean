import VixOverlap.ScheduleCertificate

/-!
The prescribed count marginals pass the overlap stop-loss tests at every real
strike. These are structural certification inequalities, not trading claims.
The proof uses the same pair witnesses and the standing prefix marginals.
-/

open scoped BigOperators

namespace VixOverlap.PairTests

open ScheduleCertificate

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Cells present in the earlier window and absent from the later window. -/
def outgoingCount (a : Schedule) (i j : Fin 3) : ℕ :=
  ∑ h : Fin 6,
    if i.val + 1 ≤ h.val ∧ h.val < j.val + 1 then bit a h else 0

theorem outgoing_slots : ∀ i j : Fin 3,
    (∑ h : Fin 6, if i.val + 1 ≤ h.val ∧ h.val < j.val + 1 then 1 else 0) =
      j.val - i.val := by decide

theorem count_domination : ∀ (a : Schedule) (i j : Fin 3), i ≤ j →
    windowCount a i ≤ windowCount a j + outgoingCount a i j := by decide

theorem outgoing_mean (p : Schedule → ℝ) (hp : PrefixMarginals p) (i j : Fin 3) :
    (∑ a, p a * (outgoingCount a i j : ℝ)) = ((j.val - i.val : ℕ) : ℝ) / 2 := by
  calc
    (∑ a, p a * (outgoingCount a i j : ℝ)) =
        ∑ h : Fin 6, ∑ a, p a *
          ((if i.val + 1 ≤ h.val ∧ h.val < j.val + 1 then bit a h else 0 : ℕ) : ℝ) := by
      simp only [outgoingCount, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ h : Fin 6,
        if i.val + 1 ≤ h.val ∧ h.val < j.val + 1 then (1 / 2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs with hh
      · exact prefix_marginals_bit_mean p hp h
      · simp
    _ = ((∑ h : Fin 6,
        if i.val + 1 ≤ h.val ∧ h.val < j.val + 1 then 1 else 0 : ℕ) : ℝ) / 2 := by
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> norm_num
    _ = ((j.val - i.val : ℕ) : ℝ) / 2 := by rw [outgoing_slots]

theorem expected_window_mean (p : Schedule → ℝ) (hp : PrefixMarginals p) (w : Fin 3) :
    (∑ a, p a * (windowCount a w : ℝ)) = 3 / 2 := by
  calc
    (∑ a, p a * (windowCount a w : ℝ)) =
        ∑ r : Fin 3, ∑ a, p a * (bit a ⟨w.val + r.val + 1, by omega⟩ : ℝ) := by
      simp only [windowCount, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _ : Fin 3, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      exact prefix_marginals_bit_mean p hp _
    _ = 3 / 2 := by norm_num

theorem real_score_expectation {I : Type*} [Fintype I]
    (p : Schedule → ℝ) (count : I → Schedule → ℕ) (atom : I → ℕ) (c : I → ℝ) :
    (∑ a, p a * (∑ i, if count i a = atom i then c i else 0)) =
      ∑ i, c i * atomMass p (count i) (atom i) := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [atomMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all [mul_comm]

theorem window_real_partition (a : Schedule) (w : Fin 3) (f : ℕ → ℝ) :
    (∑ k : Fin 4, if windowCount a w = k.val then f k.val else 0) =
      f (windowCount a w) := by
  let k0 : Fin 4 := ⟨windowCount a w, by have := windowCount_le_three a w; omega⟩
  have he : ∀ k : Fin 4, windowCount a w = k.val ↔ k = k0 := by
    intro k
    constructor
    · intro h
      exact Fin.ext h.symm
    · intro h
      subst k
      rfl
  simp_rw [he]
  simp [k0]

theorem window_expectation_by_atoms (p : Schedule → ℝ) (w : Fin 3) (f : ℕ → ℝ) :
    (∑ a, p a * f (windowCount a w)) =
      ∑ k : Fin 4, f k.val * atomMass p (fun a => windowCount a w) k.val := by
  simpa only [window_real_partition] using
    real_score_expectation p (fun (_ : Fin 4) a => windowCount a w)
      (fun k : Fin 4 => k.val) (fun k : Fin 4 => f k.val)

theorem window_marginal_expectation (p : Schedule → ℝ) (w : Fin 3) (ε : ℝ)
    (hw : WindowMarginal p w ε) (f : ℕ → ℝ) :
    (∑ a, p a * f (windowCount a w)) =
      ∑ k : Fin 4, mixedTarget ε w k * f k.val := by
  rw [window_expectation_by_atoms]
  apply Finset.sum_congr rfl
  intro k _
  rw [hw k, mul_comm]

theorem window_has_pair : ∀ w : Fin 3, ∃ b : Fin 3, pairContains b w := by
  unfold pairContains
  decide

theorem pair_has_witness : ∀ i j : Fin 3, i < j →
    ∃ b : Fin 3, pairContains b i ∧ pairContains b j := by
  unfold pairContains
  decide

/-- All three mixed targets have the required count mean, for every real
mixture parameter. Probabilities require the separate interval restriction. -/
theorem mean_count (ε : ℝ) (w : Fin 3) :
    (∑ k : Fin 4, mixedTarget ε w k * (k.val : ℝ)) = 3 / 2 := by
  obtain ⟨b, hb⟩ := window_has_pair w
  have hm := expected_window_mean (mixedWeight ε b) (mixed_prefix ε b) w
  rw [window_marginal_expectation _ w ε (mixed_window ε b w hb)
    (fun n => (n : ℝ))] at hm
  exact hm

theorem max_sub_le_add (u v d x : ℝ) (hu : u ≤ v + d) (hd : 0 ≤ d) :
    max (u - x) 0 ≤ max (v - x) 0 + d := by
  apply max_le
  · calc
      u - x ≤ (v + d) - x := sub_le_sub_right hu x
      _ = (v - x) + d := by ring
      _ ≤ max (v - x) 0 + d := add_le_add (le_max_left _ _) le_rfl
  · exact add_nonneg (le_max_right _ _) hd

theorem scaled_pointwise_overlap (a : Schedule) (i j : Fin 3) (hij : i ≤ j)
    (s x : ℝ) (hs : 0 ≤ s) :
    max (s * (windowCount a i : ℝ) - x) 0 ≤
      max (s * (windowCount a j : ℝ) - x) 0 + s * (outgoingCount a i j : ℝ) := by
  have hc : (windowCount a i : ℝ) ≤
      ((windowCount a j + outgoingCount a i j : ℕ) : ℝ) :=
    Nat.cast_le.mpr (count_domination a i j hij)
  rw [Nat.cast_add] at hc
  apply max_sub_le_add
  · simpa only [mul_add] using mul_le_mul_of_nonneg_left hc hs
  · exact mul_nonneg hs (Nat.cast_nonneg _)

/-- The structural overlap bound for every nonnegative schedule weighting with
the standing prefix marginals. The strike is unrestricted. -/
theorem expected_scaled_overlap (p : Schedule → ℝ) (hn : ∀ a, 0 ≤ p a)
    (hp : PrefixMarginals p) (i j : Fin 3) (hij : i ≤ j) (s x : ℝ) (hs : 0 ≤ s) :
    (∑ a, p a * max (s * (windowCount a i : ℝ) - x) 0) -
      (∑ a, p a * max (s * (windowCount a j : ℝ) - x) 0) ≤
        s * (((j.val : ℝ) - (i.val : ℝ)) / 2) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Schedule))
    (fun a _ => mul_le_mul_of_nonneg_left (scaled_pointwise_overlap a i j hij s x hs) (hn a))
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have ht : (∑ a, p a * (s * (outgoingCount a i j : ℝ))) =
      s * (((j.val - i.val : ℕ) : ℝ) / 2) := by
    calc
      (∑ a, p a * (s * (outgoingCount a i j : ℝ))) =
          s * ∑ a, p a * (outgoingCount a i j : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [outgoing_mean p hp i j]
  rw [ht, Nat.cast_sub (show i.val ≤ j.val from hij)] at hsum
  exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hsum)

/-- Every prescribed mixed pair passes the overlap inequality, at all real
strikes and for every nonnegative scaling of the window count. -/
theorem mixed_scaled_overlap (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (i j : Fin 3) (hij : i < j) (s x : ℝ) (hs : 0 ≤ s) :
    (∑ k : Fin 4, mixedTarget ε i k * max (s * (k.val : ℝ) - x) 0) -
      (∑ k : Fin 4, mixedTarget ε j k * max (s * (k.val : ℝ) - x) 0) ≤
        s * (((j.val : ℝ) - (i.val : ℝ)) / 2) := by
  obtain ⟨b, hi, hj⟩ := pair_has_witness i j hij
  have h := expected_scaled_overlap (mixedWeight ε b) (mixed_probability ε h0 h1 b).1
    (mixed_prefix ε b) i j hij.le s x hs
  rw [window_marginal_expectation _ i ε (mixed_window ε b i hi)
      (fun n => max (s * (n : ℝ) - x) 0),
    window_marginal_expectation _ j ε (mixed_window ε b j hj)
      (fun n => max (s * (n : ℝ) - x) 0)] at h
  exact h

theorem mixed_overlap (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (i j : Fin 3) (hij : i < j) (x : ℝ) :
    (∑ k : Fin 4, mixedTarget ε i k * max ((k.val : ℝ) - x) 0) -
      (∑ k : Fin 4, mixedTarget ε j k * max ((k.val : ℝ) - x) 0) ≤
        ((j.val : ℝ) - (i.val : ℝ)) / 2 := by
  simpa only [one_mul] using mixed_scaled_overlap ε h0 h1 i j hij 1 x zero_le_one

/-- In the three-cell idealized VIX-squared normalization, the count scale is
`c / 3`, so the outgoing expected budget divided by tenor is `c (j-i) / 6`. -/
theorem vix_squared_overlap (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (i j : Fin 3) (hij : i < j) (c x : ℝ) (hc : 0 ≤ c) :
    (∑ k : Fin 4, mixedTarget ε i k * max ((c / 3) * (k.val : ℝ) - x) 0) -
      (∑ k : Fin 4, mixedTarget ε j k * max ((c / 3) * (k.val : ℝ) - x) 0) ≤
        c * ((j.val : ℝ) - (i.val : ℝ)) / 6 := by
  have h := mixed_scaled_overlap ε h0 h1 i j hij (c / 3) x
    (div_nonneg hc (by norm_num))
  calc
    _ ≤ (c / 3) * (((j.val : ℝ) - (i.val : ℝ)) / 2) := h
    _ = c * ((j.val : ℝ) - (i.val : ℝ)) / 6 := by ring

theorem vix_squared_mean (ε : ℝ) (w : Fin 3) (c : ℝ) :
    (∑ k : Fin 4, mixedTarget ε w k * ((c / 3) * (k.val : ℝ))) = c / 2 := by
  calc
    (∑ k : Fin 4, mixedTarget ε w k * ((c / 3) * (k.val : ℝ))) =
        (c / 3) * ∑ k : Fin 4, mixedTarget ε w k * (k.val : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = c / 2 := by rw [mean_count]; ring

end VixOverlap.PairTests
