import VixOverlap.Vanilla
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.NormNum

noncomputable section

namespace VixOverlap.Vanilla

/-- A stock value in the fair active/frozen architecture identifies the number
of active cells. This uses unique prime factors, not rounded logarithms or an
assumption that latent activity is quoted. -/
theorem active_count_identified (n u m v : ℕ)
    (h : (3 : ℝ)^u / 2^n = (3 : ℝ)^v / 2^m) : n = m := by
  have hn : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm : (2 : ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (3 : ℝ)^u * 2^m = (3 : ℝ)^v * 2^n :=
    (div_eq_div_iff hn hm).mp h
  have heN : (3 : ℕ)^u * 2^m = (3 : ℕ)^v * 2^n := by exact_mod_cast he
  have hf := congrArg (fun a : ℕ => a.factorization 2) heN
  have p2 : Nat.Prime 2 := Nat.prime_two
  have p3 : Nat.Prime 3 := Nat.prime_three
  rw [Nat.factorization_mul (pow_ne_zero _ p3.ne_zero) (pow_ne_zero _ p2.ne_zero),
    Nat.factorization_mul (pow_ne_zero _ p3.ne_zero) (pow_ne_zero _ p2.ne_zero)] at hf
  simp only [p3.factorization_pow, p2.factorization_pow, Finsupp.add_apply,
    Finsupp.single_apply, show (3 : ℕ) ≠ 2 by decide, if_false, if_true, zero_add] at hf
  exact hf.symm

end VixOverlap.Vanilla
