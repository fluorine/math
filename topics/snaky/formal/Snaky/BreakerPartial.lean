import Snaky.BreakerPairing

/-!
# Partial matching defenses with actual fillers

Unmatched cells need not be artificially paired. Breaker takes the mate of
an entered unblocked pair, and otherwise any available physical cell. The
one-way matching invariant tolerates additional Breaker stones. Exhaustion
is handled by the original game's `hfree` guard, not by a virtual pass.
-/
namespace Snaky.Breaker

def WeakMateInvariant (D : Nat → Prop) (mate : Nat → Nat)
    (M W : List Nat) : Prop :=
  ∀ x, D x → x ∈ M → mate x ∈ W

def PartialOK (N : Nat) (M W domain : List Nat) (mate : Nat → Nat) : Prop :=
  ∀ x ∈ domain, Fresh N M W x ∧ mate x ∈ domain ∧
    mate x ≠ x ∧ mate (mate x) = x

def PartialCovers (P : List (List Nat)) (M W domain : List Nat)
    (mate : Nat → Nat) : Prop :=
  ∀ e ∈ P, (∀ x ∈ e, x ∉ W) → ∃ x ∈ e, x ∈ domain ∧ mate x ∈ e

theorem partial_frame {N : Nat} {M W domain : List Nat} {mate : Nat → Nat}
    (h : PartialOK N M W domain mate) : MateFrame N (fun x => x ∈ domain) mate := by
  intro x hx
  have h₁ := h x hx
  have h₂ := h (mate x) h₁.2.1
  exact ⟨h₂.1.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2⟩

theorem weak_mate_step {D : Nat → Prop} {mate : Nat → Nat} {M W : List Nat}
    (h : WeakMateInvariant D mate M W) (u : Nat) :
    WeakMateInvariant D mate (u :: M) (mate u :: W) := by
  intro x hx hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h x hx hm)

theorem weak_breaker_step {D : Nat → Prop} {mate : Nat → Nat} {M W : List Nat}
    (h : WeakMateInvariant D mate M W) (v : Nat) :
    WeakMateInvariant D mate M (v :: W) := by
  intro x hx hm
  exact List.mem_cons_of_mem _ (h x hx hm)

def PartialState (M₀ W₀ domain : List Nat) (mate : Nat → Nat)
    (M W : List Nat) : Prop :=
  Extends M₀ M ∧ Extends W₀ W ∧ Disjoint M W ∧
    WeakMateInvariant (fun x => x ∈ domain) mate M W

theorem partial_state_cover {P : List (List Nat)} {N : Nat}
    {M₀ W₀ domain M W : List Nat} {mate : Nat → Nat}
    (hok : PartialOK N M₀ W₀ domain mate)
    (hcover : PartialCovers P M₀ W₀ domain mate)
    (hs : PartialState M₀ W₀ domain mate M W) : TwoFreshCover P N M W := by
  intro e he hlive
  obtain ⟨x, hxe, hxD, hye⟩ := hcover e he
    (fun y hy hyW => hlive y hy (hs.2.1 y hyW))
  have hf := partial_frame hok
  have hyD := (hf x hxD).2.1
  refine ⟨x, mate x, hxe, hye, (hf x hxD).2.2.1.symm, ?_, ?_⟩
  · exact ⟨(hok x hxD).1.1, fun hm => hlive (mate x) hye (hs.2.2.2 x hxD hm),
      hlive x hxe⟩
  · refine ⟨(hf x hxD).1, ?_, hlive (mate x) hye⟩
    intro hm
    have hw := hs.2.2.2 (mate x) hyD hm
    rw [(hf x hxD).2.2.2] at hw
    exact hlive x hxe hw

/-- Full physical defense from a partial matching, with arbitrary fresh fillers. -/
theorem partial_matching_not_blackWins {P : List (List Nat)} {N : Nat}
    {M₀ W₀ domain : List Nat} {mate : Nat → Nat}
    (hd : Disjoint M₀ W₀) (hok : PartialOK N M₀ W₀ domain mate)
    (hcover : PartialCovers P M₀ W₀ domain mate) : ¬ BlackWins P N M₀ W₀ := by
  let I := PartialState M₀ W₀ domain mate
  have hf := partial_frame hok
  have step : InvariantStep P N I := by
    intro M W hs u hu
    refine ⟨noComplete_after_of_twoFresh hs.2.2.1 hu
      (partial_state_cover hok hcover hs), ?_⟩
    intro hfree
    by_cases huD : u ∈ domain
    · by_cases hmateW : mate u ∈ W
      · obtain ⟨v, hv⟩ := hfree
        refine ⟨v, hv, Or.inl ⟨extends_cons hs.1 u, extends_cons hs.2.1 v,
          disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv, ?_⟩⟩
        apply weak_breaker_step
        intro x hx hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hmateW
        · exact hs.2.2.2 x hx hm
      · have hv₀ : Fresh N M W (mate u) := by
          refine ⟨(hf u huD).1, ?_, hmateW⟩
          intro hm
          have hw := hs.2.2.2 (mate u) (hf u huD).2.1 hm
          rw [(hf u huD).2.2.2] at hw
          exact hu.2.2 hw
        have hv := fresh_cons_maker hv₀ (hf u huD).2.2.1
        refine ⟨mate u, hv, Or.inl ⟨extends_cons hs.1 u, extends_cons hs.2.1 (mate u),
          disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv,
          weak_mate_step hs.2.2.2 u⟩⟩
    · obtain ⟨v, hv⟩ := hfree
      refine ⟨v, hv, Or.inl ⟨extends_cons hs.1 u, extends_cons hs.2.1 v,
        disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv, ?_⟩⟩
      apply weak_breaker_step
      intro x hx hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact False.elim (huD hx)
      · exact hs.2.2.2 x hx hm
  apply invariant_not_blackWins step
  refine ⟨fun _ h => h, fun _ h => h, hd, ?_⟩
  intro x hx hm
  exact False.elim ((hok x hx).1.2.1 hm)

end Snaky.Breaker
