import Snaky.Game

/-!
# Monotone finite-core coverage certificates

This file proves a combinatorial replacement lemma. It does not assume that
ghost ownership is physical ownership, nor infer a game outcome from coverage.
The concrete e1 instances supply explicit necessary membership constraints.
-/
namespace Snaky.E1

abbrev Pair := Nat × Nat

def covered (pairs : List Pair) (trace : List Nat) : Bool :=
  pairs.any fun p => trace.contains p.1 && trace.contains p.2

structure CoreCase where
  positive : List Nat
  negative : List Nat
  forbidden : List (List Nat)
  pairs : List Pair
  deriving Repr, DecidableEq

def Compatible (c : CoreCase) (K : List Nat) : Prop :=
  c.positive.Subset K ∧ (∀ x ∈ c.negative, x ∉ K) ∧
    ∀ f ∈ c.forbidden, ¬ f.Subset K

def rejected (c : CoreCase) (trace : List Nat) : Bool :=
  let minimum := c.positive ++ trace
  minimum.any (fun x => c.negative.contains x) ||
    c.forbidden.any (fun f => f.all (fun x => minimum.contains x))

theorem rejected_incompatible {c : CoreCase} {trace K : List Nat}
    (hc : Compatible c K) (ht : trace.Subset K) : rejected c trace = false := by
  have hmin : (c.positive ++ trace).Subset K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hc.1 hx
    · exact ht hx
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [rejected, Bool.or_eq_true, List.any_eq_true, List.contains_iff,
    List.all_eq_true] at h
  rcases h with ⟨x, hx, hn⟩ | ⟨f, hf, hs⟩
  · exact hc.2.1 x hn (hmin hx)
  · exact hc.2.2 f hf (fun x hx => hmin (hs x hx))

theorem covered_witness {pairs : List Pair} {trace : List Nat}
    (h : covered pairs trace = true) :
    ∃ p ∈ pairs, p.1 ∈ trace ∧ p.2 ∈ trace := by
  simpa only [covered, List.any_eq_true, Bool.and_eq_true, List.contains_iff] using h

/-- Checking only the uncovered traces is sufficient; the remaining membership
bits of K are arbitrary. This is the minimal-core argument, not a sampling claim. -/
theorem coverage_of_uncovered_check {c : CoreCase} {sources : List (List Nat)}
    (hcheck : ((sources.filter fun t => !covered c.pairs t).all
      (rejected c)) = true)
    {K trace : List Nat} (hc : Compatible c K) (hs : trace ∈ sources)
    (ht : trace.Subset K) : ∃ p ∈ c.pairs,
      p.1 ∈ trace ∧ p.2 ∈ trace ∧ p.1 ∈ K ∧ p.2 ∈ K := by
  have hcover : covered c.pairs trace = true := by
    cases hb : covered c.pairs trace with
    | true => rfl
    | false =>
      have hm : trace ∈ sources.filter (fun t => !covered c.pairs t) := by
        simp only [List.mem_filter, hs, hb, Bool.not_false, and_self]
      have hbad := List.all_eq_true.mp hcheck trace hm
      rw [rejected_incompatible hc ht] at hbad
      contradiction
  obtain ⟨p, hp, ha, hb⟩ := covered_witness hcover
  exact ⟨p, hp, ha, hb, ht ha, ht hb⟩

/-- Whole-source inclusion in a physical target preserves its covering pair.
No self-source assumption is made, so cross-source incidences are included. -/
theorem coverage_transfers {c : CoreCase} {sources : List (List Nat)}
    (hcheck : ((sources.filter fun t => !covered c.pairs t).all
      (rejected c)) = true)
    {K trace target : List Nat} (hc : Compatible c K) (hs : trace ∈ sources)
    (ht : trace.Subset K) (he : trace.Subset target) :
    ∃ p ∈ c.pairs, p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ∈ target ∧ p.2 ∈ target := by
  obtain ⟨p, hp, ha, hb, hka, hkb⟩ := coverage_of_uncovered_check hcheck hc hs ht
  exact ⟨p, hp, hka, hkb, he ha, he hb⟩

end Snaky.E1
