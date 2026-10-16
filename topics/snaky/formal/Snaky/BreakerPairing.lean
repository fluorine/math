import Snaky.BreakerSafety

/-!
# Total matching defenses

A fixed involution on the initially fresh cells is a legal complete mate
strategy when every initially live target contains one of its pairs.
The invariant equates each new Maker endpoint with its Breaker mate. This
proves safety immediately after every Maker claim, including the last claim.
-/
namespace Snaky.Breaker

/-- An untrusted literal pair list is converted to a total function. The
fixed-point fallback is harmless only where the checked hypotheses permit it. -/
def mateOfPairs : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | (a, b) :: ps, x => if x = a then b else if x = b then a else mateOfPairs ps x

def MateFrame (N : Nat) (D : Nat → Prop) (mate : Nat → Nat) : Prop :=
  ∀ x, D x → mate x < N ∧ D (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x

def MateInvariant (D : Nat → Prop) (mate : Nat → Nat) (M W : List Nat) : Prop :=
  ∀ x, D x → (x ∈ M ↔ mate x ∈ W)

theorem mate_injective {N : Nat} {D : Nat → Prop} {mate : Nat → Nat}
    (frame : MateFrame N D mate) {x y : Nat} (hx : D x) (hy : D y)
    (h : mate x = mate y) : x = y := by
  have h' := congrArg mate h
  simpa only [(frame x hx).2.2.2, (frame y hy).2.2.2] using h'

theorem mate_fresh {N x : Nat} {D : Nat → Prop} {mate : Nat → Nat}
    {M W : List Nat} (frame : MateFrame N D mate)
    (hinv : MateInvariant D mate M W) (hxD : D x) (hx : Fresh N M W x) :
    Fresh N M W (mate x) := by
  have hf := frame x hxD
  refine ⟨hf.1, ?_, ?_⟩
  · intro hm
    have hw := (hinv (mate x) hf.2.1).1 hm
    rw [hf.2.2.2] at hw
    exact hx.2.2 hw
  · intro hw
    exact hx.2.1 ((hinv x hxD).2 hw)

theorem mate_invariant_step {N u : Nat} {D : Nat → Prop} {mate : Nat → Nat}
    {M W : List Nat} (frame : MateFrame N D mate)
    (hinv : MateInvariant D mate M W) (huD : D u) :
    MateInvariant D mate (u :: M) (mate u :: W) := by
  intro x hxD
  simp only [List.mem_cons]
  constructor
  · intro h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ((hinv x hxD).1 h)
  · intro h
    rcases h with h | h
    · exact Or.inl (mate_injective frame hxD huD h)
    · exact Or.inr ((hinv x hxD).2 h)

theorem pair_fresh_of_live {N x : Nat} {D : Nat → Prop} {mate : Nat → Nat}
    {M W : List Nat} (frame : MateFrame N D mate)
    (hinv : MateInvariant D mate M W) (hxD : D x) (hxN : x < N)
    (hxW : x ∉ W) (hyW : mate x ∉ W) :
    Fresh N M W x ∧ Fresh N M W (mate x) := by
  have hxf : Fresh N M W x := ⟨hxN, fun hm => hyW ((hinv x hxD).1 hm), hxW⟩
  exact ⟨hxf, mate_fresh frame hinv hxD hxf⟩

def MatchingOK (N : Nat) (M W : List Nat) (mate : Nat → Nat) : Prop :=
  ∀ x ∈ List.range N, x ∉ M → x ∉ W →
    Fresh N M W (mate x) ∧ mate x ≠ x ∧ mate (mate x) = x

def MatchingCovers (P : List (List Nat)) (N : Nat)
    (M W : List Nat) (mate : Nat → Nat) : Prop :=
  ∀ e ∈ P, (∀ x ∈ e, x ∉ W) → ∃ x ∈ e, Fresh N M W x ∧ mate x ∈ e

theorem matching_frame {N : Nat} {M W : List Nat} {mate : Nat → Nat}
    (h : MatchingOK N M W mate) : MateFrame N (Fresh N M W) mate := by
  intro x hx
  obtain ⟨hy, hne, hi⟩ := h x (List.mem_range.mpr hx.1) hx.2.1 hx.2.2
  exact ⟨hy.1, hy, hne, hi⟩

def MatchingState (N : Nat) (M₀ W₀ : List Nat) (mate : Nat → Nat)
    (M W : List Nat) : Prop :=
  Extends M₀ M ∧ Extends W₀ W ∧ Disjoint M W ∧
    MateInvariant (Fresh N M₀ W₀) mate M W

theorem matching_state_cover {P : List (List Nat)} {N : Nat}
    {M₀ W₀ M W : List Nat} {mate : Nat → Nat}
    (hmate : MatchingOK N M₀ W₀ mate) (hcover : MatchingCovers P N M₀ W₀ mate)
    (hs : MatchingState N M₀ W₀ mate M W) : TwoFreshCover P N M W := by
  intro e he hlive
  obtain ⟨x, hx, hxf, hye⟩ := hcover e he (fun y hy hyW => hlive y hy (hs.2.1 y hyW))
  have hf := matching_frame hmate
  have pair := pair_fresh_of_live hf hs.2.2.2 hxf hxf.1 (hlive x hx) (hlive (mate x) hye)
  exact ⟨x, mate x, hx, hye, (hf x hxf).2.2.1.symm, pair.1, pair.2⟩

/-- A complete physical defense from exactly the supplied initial colors. -/
theorem matching_not_blackWins {P : List (List Nat)} {N : Nat}
    {M₀ W₀ : List Nat} {mate : Nat → Nat}
    (hd : Disjoint M₀ W₀) (hmate : MatchingOK N M₀ W₀ mate)
    (hcover : MatchingCovers P N M₀ W₀ mate) : ¬ BlackWins P N M₀ W₀ := by
  let I := MatchingState N M₀ W₀ mate
  have hf := matching_frame hmate
  have step : InvariantStep P N I := by
    intro M W hs u hu
    have hu₀ := fresh_of_extends hs.1 hs.2.1 hu
    have hv := mate_fresh hf hs.2.2.2 hu₀ hu
    have hv' := fresh_cons_maker hv (hf u hu₀).2.2.1
    refine ⟨noComplete_after_of_twoFresh hs.2.2.1 hu (matching_state_cover hmate hcover hs), ?_⟩
    intro _
    refine ⟨mate u, hv', Or.inl ?_⟩
    exact ⟨extends_cons hs.1 u, extends_cons hs.2.1 (mate u),
      disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv',
      mate_invariant_step hf hs.2.2.2 hu₀⟩
  apply invariant_not_blackWins step
  refine ⟨fun _ h => h, fun _ h => h, hd, ?_⟩
  intro x hx
  constructor
  · intro hxM
    exact False.elim (hx.2.1 hxM)
  · intro hxW
    exact False.elim ((hf x hx).2.1.2.2 hxW)

end Snaky.Breaker
