import Snaky.BreakerPairing

/-!
# A pristine component switching to a matching

Outside the reserved domain, Breaker uses a total matching. On the first
Maker entry into the reserved domain, a checked reply and local matching
replace the component. The whole domain stays pristine before this entry.
All claims use the original finite-board game, with no passes or erased colors.
-/
namespace Snaky.Breaker

def OuterDomain (N : Nat) (M W R : List Nat) (x : Nat) : Prop :=
  Fresh N M W x ∧ x ∉ R

def OuterOK (N : Nat) (M W R : List Nat) (mate : Nat → Nat) : Prop :=
  ∀ x ∈ List.range N, x ∉ M → x ∉ W → x ∉ R →
    Fresh N M W (mate x) ∧ mate x ∉ R ∧ mate x ≠ x ∧ mate (mate x) = x

theorem outer_frame {N : Nat} {M W R : List Nat} {mate : Nat → Nat}
    (h : OuterOK N M W R mate) : MateFrame N (OuterDomain N M W R) mate := by
  intro x hx
  obtain ⟨hy, hyr, hne, hinv⟩ := h x (List.mem_range.mpr hx.1.1) hx.1.2.1 hx.1.2.2 hx.2
  exact ⟨hy.1, ⟨hy, hyr⟩, hne, hinv⟩

def GuardOK (R : List Nat) (guards : List (List Nat)) : Prop :=
  ∀ g ∈ guards, (∀ x ∈ g, x ∈ R) ∧ ∃ x ∈ g, ∃ y ∈ g, x ≠ y

def SwitchOK (R : List Nat) (guards : List (List Nat))
    (reply : Nat → Nat) (localMate : Nat → Nat → Nat) : Prop :=
  ∀ u ∈ R,
    reply u ∈ R ∧ reply u ≠ u ∧
    (∀ x ∈ R, x ≠ u → x ≠ reply u →
      localMate u x ∈ R ∧ localMate u x ≠ u ∧ localMate u x ≠ reply u ∧
      localMate u x ≠ x ∧ localMate u (localMate u x) = x) ∧
    (∀ g ∈ guards, reply u ∈ g ∨
      ∃ x ∈ g, x ∈ R ∧ x ≠ u ∧ x ≠ reply u ∧ localMate u x ∈ g)

def WaitingCovers (P : List (List Nat)) (N : Nat) (M W R : List Nat)
    (guards : List (List Nat)) (mate : Nat → Nat) : Prop :=
  ∀ e ∈ P, (∀ x ∈ e, x ∉ W) →
    (∃ x ∈ e, OuterDomain N M W R x ∧ mate x ∈ e) ∨
    (∃ g ∈ guards, ∀ x ∈ g, x ∈ e)

def WaitingState (N : Nat) (M₀ W₀ R : List Nat) (mate : Nat → Nat)
    (M W : List Nat) : Prop :=
  Extends M₀ M ∧ Extends W₀ W ∧ Disjoint M W ∧
    (∀ x ∈ R, Fresh N M W x) ∧ MateInvariant (OuterDomain N M₀ W₀ R) mate M W

theorem outside_ne_inside {R : List Nat} {x y : Nat} (hx : x ∉ R) (hy : y ∈ R) :
    x ≠ y := by
  intro h
  subst x
  exact hx hy

theorem waiting_state_cover {P : List (List Nat)} {N : Nat}
    {M₀ W₀ R M W : List Nat} {guards : List (List Nat)} {mate : Nat → Nat}
    (houter : OuterOK N M₀ W₀ R mate) (hguards : GuardOK R guards)
    (hcover : WaitingCovers P N M₀ W₀ R guards mate)
    (hs : WaitingState N M₀ W₀ R mate M W) : TwoFreshCover P N M W := by
  intro e he hlive
  have hlive₀ : ∀ x ∈ e, x ∉ W₀ := fun x hx hxW => hlive x hx (hs.2.1 x hxW)
  rcases hcover e he hlive₀ with ⟨x, hx, hxD, hye⟩ | ⟨g, hg, hge⟩
  · have hf := outer_frame houter
    have pair := pair_fresh_of_live hf hs.2.2.2.2 hxD hxD.1.1
      (hlive x hx) (hlive (mate x) hye)
    exact ⟨x, mate x, hx, hye, (hf x hxD).2.2.1.symm, pair.1, pair.2⟩
  · obtain ⟨x, hxg, y, hyg, hne⟩ := (hguards g hg).2
    exact ⟨x, y, hge x hxg, hge y hyg, hne,
      hs.2.2.2.1 x ((hguards g hg).1 x hxg),
      hs.2.2.2.1 y ((hguards g hg).1 y hyg)⟩

theorem waiting_outside_step {N u : Nat} {M₀ W₀ R M W : List Nat}
    {mate : Nat → Nat} (houter : OuterOK N M₀ W₀ R mate)
    (hs : WaitingState N M₀ W₀ R mate M W)
    (hu : Fresh N M W u) (huR : u ∉ R) :
    Fresh N (u :: M) W (mate u) ∧
      WaitingState N M₀ W₀ R mate (u :: M) (mate u :: W) := by
  have hf := outer_frame houter
  have huD : OuterDomain N M₀ W₀ R u := ⟨fresh_of_extends hs.1 hs.2.1 hu, huR⟩
  have hv := mate_fresh hf hs.2.2.2.2 huD hu
  have hv' := fresh_cons_maker hv (hf u huD).2.2.1
  refine ⟨hv', extends_cons hs.1 u, extends_cons hs.2.1 (mate u),
    disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv', ?_,
    mate_invariant_step hf hs.2.2.2.2 huD⟩
  intro x hxR
  exact fresh_cons_both (hs.2.2.2.1 x hxR)
    (outside_ne_inside huR hxR).symm
    (outside_ne_inside (hf u huD).2.1.2 hxR).symm

def switchedMate (R : List Nat) (mate : Nat → Nat) (localMate : Nat → Nat → Nat)
    (u x : Nat) : Nat := if x ∈ R then localMate u x else mate x

theorem waiting_switch_matching {P : List (List Nat)} {N u : Nat}
    {M₀ W₀ R M W : List Nat} {guards : List (List Nat)}
    {mate reply : Nat → Nat} {localMate : Nat → Nat → Nat}
    (houter : OuterOK N M₀ W₀ R mate) (hswitch : SwitchOK R guards reply localMate)
    (hcover : WaitingCovers P N M₀ W₀ R guards mate)
    (hs : WaitingState N M₀ W₀ R mate M W) (huR : u ∈ R) :
    Fresh N (u :: M) W (reply u) ∧
    MatchingOK N (u :: M) (reply u :: W) (switchedMate R mate localMate u) ∧
    MatchingCovers P N (u :: M) (reply u :: W) (switchedMate R mate localMate u) := by
  have row := hswitch u huR
  have hu := hs.2.2.2.1 u huR
  have hv := hs.2.2.2.1 (reply u) row.1
  have hv' := fresh_cons_maker hv row.2.1
  have hf := outer_frame houter
  refine ⟨hv', ?_, ?_⟩
  · intro x hxN hxM hxW
    have hxf : Fresh N (u :: M) (reply u :: W) x := ⟨List.mem_range.mp hxN, hxM, hxW⟩
    have hxu : x ≠ u := fun h => hxM (List.mem_cons.mpr (Or.inl h))
    have hxv : x ≠ reply u := fun h => hxW (List.mem_cons.mpr (Or.inl h))
    by_cases hxR : x ∈ R
    · have hlocalData := row.2.2.1 x hxR hxu hxv
      have hlocal := fresh_cons_both (hs.2.2.2.1 (localMate u x) hlocalData.1)
        hlocalData.2.1 hlocalData.2.2.1
      simpa only [switchedMate, if_pos hxR, if_pos hlocalData.1] using
        And.intro hlocal (And.intro hlocalData.2.2.2.1 hlocalData.2.2.2.2)
    · have hxc : Fresh N M W x := ⟨hxf.1,
        fun h => hxM (List.mem_cons_of_mem u h),
        fun h => hxW (List.mem_cons_of_mem (reply u) h)⟩
      have hxD : OuterDomain N M₀ W₀ R x := ⟨fresh_of_extends hs.1 hs.2.1 hxc, hxR⟩
      have hyR := (hf x hxD).2.1.2
      have hy := mate_fresh hf hs.2.2.2.2 hxD hxc
      have hy' := fresh_cons_both hy (outside_ne_inside hyR huR) (outside_ne_inside hyR row.1)
      simpa only [switchedMate, if_neg hxR, if_neg hyR] using
        And.intro hy' (And.intro (hf x hxD).2.2.1 (hf x hxD).2.2.2)
  · intro e he hlive
    have hlive₀ : ∀ x ∈ e, x ∉ W₀ :=
      fun x hx hxW => hlive x hx (List.mem_cons_of_mem (reply u) (hs.2.1 x hxW))
    rcases hcover e he hlive₀ with ⟨x, hx, hxD, hye⟩ | ⟨g, hg, hge⟩
    · have hlivec : ∀ z ∈ e, z ∉ W :=
        fun z hz hzW => hlive z hz (List.mem_cons_of_mem (reply u) hzW)
      have hxf := (pair_fresh_of_live hf hs.2.2.2.2 hxD hxD.1.1
        (hlivec x hx) (hlivec (mate x) hye)).1
      have hxf' := fresh_cons_both hxf (outside_ne_inside hxD.2 huR)
        (outside_ne_inside hxD.2 row.1)
      exact ⟨x, hx, hxf', by simpa only [switchedMate, if_neg hxD.2] using hye⟩
    · rcases row.2.2.2 g hg with hvg | ⟨x, hxg, hxR, hxu, hxv, hyg⟩
      · exact False.elim (hlive (reply u) (hge _ hvg) (List.mem_cons_self))
      · refine ⟨x, hge x hxg, fresh_cons_both (hs.2.2.2.1 x hxR) hxu hxv, ?_⟩
        simpa only [switchedMate, if_pos hxR] using hge (localMate u x) hyg

/-- A whole-board defense using an exterior matching and one pristine switch. -/
theorem pristine_switch_not_blackWins {P : List (List Nat)} {N : Nat}
    {M₀ W₀ R : List Nat} {guards : List (List Nat)}
    {mate reply : Nat → Nat} {localMate : Nat → Nat → Nat}
    (hd : Disjoint M₀ W₀) (hr : ∀ x ∈ R, Fresh N M₀ W₀ x)
    (houter : OuterOK N M₀ W₀ R mate) (hguards : GuardOK R guards)
    (hswitch : SwitchOK R guards reply localMate)
    (hcover : WaitingCovers P N M₀ W₀ R guards mate) :
    ¬ BlackWins P N M₀ W₀ := by
  let I := WaitingState N M₀ W₀ R mate
  have step : InvariantStep P N I := by
    intro M W hs u hu
    refine ⟨noComplete_after_of_twoFresh hs.2.2.1 hu
      (waiting_state_cover houter hguards hcover hs), ?_⟩
    intro _
    by_cases huR : u ∈ R
    · obtain ⟨hv, hmatching, hcoverage⟩ := waiting_switch_matching houter hswitch hcover hs huR
      refine ⟨reply u, hv, Or.inr ?_⟩
      exact matching_not_blackWins
        (disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv) hmatching hcoverage
    · obtain ⟨hv, hs'⟩ := waiting_outside_step houter hs hu huR
      exact ⟨mate u, hv, Or.inl hs'⟩
  apply invariant_not_blackWins step
  refine ⟨fun _ h => h, fun _ h => h, hd, hr, ?_⟩
  intro x hx
  constructor
  · intro hxM
    exact False.elim (hx.1.2.1 hxM)
  · intro hxW
    exact False.elim ((outer_frame houter x hx).2.1.1.2.2 hxW)

end Snaky.Breaker
