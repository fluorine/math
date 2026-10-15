import Snaky.CardsSound

/-!
# The bounded Maker--Breaker game on the infinite square board

Cells are integer pairs. Both histories are finite lists, and each player must
claim a cell absent from both histories. Maker starts; Breaker only blocks.
`PlaneBlackWinsIn n B W` counts Maker claims, including the winning claim.
Every legal integer-pair Breaker reply is quantified, with no finite envelope.

The definitions follow `Snaky.Bounded` with the finite-board restriction
removed. As there, a Black-to-move derivation starts with a legal Black claim;
the already-won alternative is available immediately after that claim. The
empty-board theorem therefore has the usual at-most-n-Maker-moves meaning.

The card soundness proof below does not infer the infinite-board result from
finite-board monotonicity. It directly handles inside- and outside-support
replies on the plane. If a pivot is already owned, Maker claims a genuinely
fresh cell; that claim is charged to the height bound.
-/

namespace Snaky

/-- The exact six-cell Snaky, allowing every translated rotation/reflection. -/
def PlaneWon (B : List Pt) : Prop :=
  ∃ f ∈ orientations snaky, ∃ t : Pt, ∀ u ∈ f, shift t u ∈ B

mutual
/-- Maker to move on `Int × Int`, with at most `n` further Maker claims. -/
inductive PlaneBlackWinsIn : Nat → List Pt → List Pt → Prop
  | move (n : Nat) (B W : List Pt) (b : Pt) (hB : b ∉ B) (hW : b ∉ W)
      (h : PlaneWhiteToMoveLosesIn n (b :: B) W) : PlaneBlackWinsIn (n + 1) B W

/-- After a Maker claim: an exact Snaky is owned, or every legal Breaker
reply leaves a win with the remaining Maker budget. -/
inductive PlaneWhiteToMoveLosesIn : Nat → List Pt → List Pt → Prop
  | won (n : Nat) (B W : List Pt) (h : PlaneWon B) : PlaneWhiteToMoveLosesIn n B W
  | reply (n : Nat) (B W : List Pt) (hfree : ∃ w : Pt, w ∉ B ∧ w ∉ W)
      (h : ∀ w : Pt, w ∉ B → w ∉ W → PlaneBlackWinsIn n B (w :: W)) :
      PlaneWhiteToMoveLosesIn n B W
end

/-- A claim cannot be hidden in a zero Maker-move budget. -/
theorem not_planeBlackWinsIn_zero (B W : List Pt) : ¬ PlaneBlackWinsIn 0 B W := nofun

/-- Any two finite histories leave a fresh integer-pair cell. -/
theorem exists_plane_free (B W : List Pt) : ∃ q : Pt, q ∉ B ∧ q ∉ W := by
  let BN := B.map (fun q => q.1.toNat)
  let WN := W.map (fun q => q.1.toNat)
  obtain ⟨n, _, hnB, hnW⟩ := exists_free
    (B := BN) (W := WN) (N := (BN ++ WN).length + 1) (Nat.lt_succ_self _)
  refine ⟨((n : Int), 0), ?_, ?_⟩
  · intro h
    apply hnB
    simpa [BN] using List.mem_map_of_mem (f := fun q : Pt => q.1.toNat) h
  · intro h
    apply hnW
    simpa [WN] using List.mem_map_of_mem (f := fun q : Pt => q.1.toNat) h

/-- The eight square symmetries carry each normalized Snaky orientation to
a translate of another. This is a finite kernel-checked identity. -/
private theorem plane_orient_image :
    ∀ m ∈ orients, ∀ f ∈ orientations snaky, ∃ f' ∈ orientations snaky,
      f.map (mApp m) = f'.map (shift
        ((mApp m (f.headD (0, 0))).1 - (f'.headD (0, 0)).1,
         (mApp m (f.headD (0, 0))).2 - (f'.headD (0, 0)).2)) := by
  decide +kernel

/-- A checked terminal remains an exact plane Snaky under an allowed card
transform and in the presence of arbitrary extra Maker stones. -/
theorem won_plane_image {L B : List Pt} (hw : wonPlane L = true) {g : Xf}
    (hg : g.isOrient = true) (howned : ∀ q ∈ L, g.app q ∈ B) : PlaneWon B := by
  unfold wonPlane at hw
  simp only [List.any_eq_true, List.all_eq_true, List.contains_iff_mem] at hw
  obtain ⟨f, hf, q0, _, hfin⟩ := hw
  obtain ⟨t, hin⟩ : ∃ t, ∀ u ∈ f, shift t u ∈ L :=
    ⟨(q0.1 - (f.headD (0, 0)).1, q0.2 - (f.headD (0, 0)).2), fun u hu => by
      have := hfin u hu
      simpa [shift] using this⟩
  rw [Xf.isOrient_iff] at hg
  obtain ⟨f', hf', himg⟩ := plane_orient_image _ hg f hf
  generalize hc :
    ((mApp (g.a, g.b, g.c, g.d) (f.headD (0, 0))).1 - (f'.headD (0, 0)).1,
     (mApp (g.a, g.b, g.c, g.d) (f.headD (0, 0))).2 - (f'.headD (0, 0)).2) = c at himg
  have hlist : f.map (fun u => g.app (shift t u)) =
      f'.map (shift (shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c))) := by
    have : (fun u => g.app (shift t u)) =
        (shift (g.dx, g.dy) ∘ shift (mApp (g.a, g.b, g.c, g.d) t)) ∘
          mApp (g.a, g.b, g.c, g.d) := by
      funext u
      simp [Xf.app_eq, mApp_shift]
    rw [this, ← List.map_map, himg, List.map_map]
    congr 1
    funext v
    simp [shift_shift]
  refine ⟨f', hf', shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c), ?_⟩
  intro v hv
  have : shift (shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c)) v ∈
      f.map (fun u => g.app (shift t u)) := by
    rw [hlist]
    exact List.mem_map_of_mem hv
  obtain ⟨u, hu, e⟩ := List.mem_map.1 this
  rw [← e]
  exact howned _ (hin u hu)

/-- Card placement invariant on the plane. Supports may contain Maker stones;
they need only avoid all Breaker stones. -/
def PlanePlaced (c : Card) (g : Xf) (B W : List Pt) : Prop :=
  (∀ a ∈ c.A, g.app a ∈ B) ∧ ∀ s ∈ c.S, g.app s ∉ W

/-- Direct soundness of every checked card against all legal integer-pair
replies, proved by induction on the Maker-move budget. -/
theorem sound_plane_aux {get : Nat → Option Card}
    (hall : ∀ j c, get j = some c → cardOK get c = true) :
    ∀ n, ∀ c : Card, (∃ j : Nat, get j = some c) → c.h ≤ n →
      ∀ g : Xf, g.isOrient = true → ∀ B W, PlanePlaced c g B W →
        PlaneBlackWinsIn n B W := by
  intro n
  induction n with
  | zero =>
    intro c ⟨j, hj⟩ hn
    have hok := hall _ _ hj
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  | succ n ih =>
    intro c ⟨j, hj⟩ hn g hg B W ⟨hAinv, hSinv⟩
    have hok := hall _ _ hj
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      List.contains_iff_mem] at hok
    obtain ⟨⟨h1, hpS⟩, hrest⟩ := hok
    have hpW := hSinv c.p hpS
    obtain ⟨b, hbB, hbW, hcov⟩ :
        ∃ b : Pt, b ∉ B ∧ b ∉ W ∧ g.app c.p ∈ b :: B := by
      by_cases hpB : g.app c.p ∈ B
      · obtain ⟨x, hxB, hxW⟩ := exists_plane_free B W
        exact ⟨x, hxB, hxW, List.mem_cons_of_mem _ hpB⟩
      · exact ⟨_, hpB, hpW, List.mem_cons_self⟩
    apply PlaneBlackWinsIn.move n B W b hbB hbW
    have hBl : ∀ q ∈ c.p :: c.A, g.app q ∈ b :: B := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hqA
      · exact hcov
      · exact List.mem_cons_of_mem _ (hAinv q hqA)
    rcases hrest with hwon | ⟨hpass, hreps⟩
    · exact PlaneWhiteToMoveLosesIn.won _ _ _ (won_plane_image hwon hg hBl)
    · apply PlaneWhiteToMoveLosesIn.reply
      · exact exists_plane_free _ _
      intro w hwB hwW
      have step : ∀ (hn : Hint) (Rg : Pt → Bool),
          (∀ s, Rg s = true → s ∈ c.S ∧ g.app s ≠ w) →
          hintOK get c.h (c.p :: c.A) Rg hn = true →
          PlaneBlackWinsIn n (b :: B) (w :: W) := by
        intro hn Rg hRg hhint
        obtain ⟨c', hj', hlt', hor, hA', hS'⟩ := hintOK_spec hhint
        refine ih c' ⟨_, hj'⟩ (by omega) (g.comp hn.2)
          (Xf.isOrient_comp hg hor) _ _ ⟨?_, ?_⟩
        · intro a ha
          rw [Xf.app_comp]
          exact hBl _ (hA' a ha)
        · intro s hs
          rw [Xf.app_comp]
          obtain ⟨hsS, hne⟩ := hRg _ (hS' s hs)
          rw [List.mem_cons, not_or]
          exact ⟨hne, hSinv _ hsS⟩
      by_cases hex : ∃ w0 ∈ c.S, g.app w0 = w
      · obtain ⟨w0, hw0S, rfl⟩ := hex
        have hw0 : w0 ∉ c.p :: c.A := fun hm => hwB (hBl w0 hm)
        have hr := List.all_eq_true.1 hreps w0 hw0S
        have hw0' : (c.p :: c.A).contains w0 = false := by
          simpa [List.contains_iff_mem] using hw0
        unfold replyOK at hr
        rw [hw0', Bool.false_or] at hr
        split at hr
        · rename_i hn _
          refine step hn _ (fun s hs => ?_) hr
          simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hs
          exact ⟨hs.1, fun e => hs.2 (Xf.app_inj hg e)⟩
        · simp at hr
      · unfold passOK at hpass
        split at hpass
        · rename_i hn _
          refine step hn _ (fun s hs => ?_) hpass
          rw [List.contains_iff_mem] at hs
          exact ⟨hs, fun e => hex ⟨s, hs, e⟩⟩
        · simp at hpass

/-- Any accepted empty-board root, with height at most `k`, forces Snaky on
the infinite square board within `k` Maker claims. Its finite-board size
premises are unused by the plane argument. -/
theorem cards_sound_plane_in {get : Nat → Option Card} {R C i k : Nat} {g : Xf}
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (hroot : rootOK get R C i g = true)
    (hk : (get i).all (fun c => decide (c.h ≤ k)) = true) :
    PlaneBlackWinsIn k [] [] := by
  unfold rootOK at hroot
  split at hroot
  · rename_i c hc
    simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
      decide_eq_true_eq] at hroot
    obtain ⟨⟨⟨hA, hg⟩, _⟩, _⟩ := hroot
    rw [hc] at hk
    simp only [Option.all_some, decide_eq_true_eq] at hk
    refine sound_plane_aux hall k c ⟨i, hc⟩ hk g hg [] [] ⟨?_, ?_⟩
    · simp [hA]
    · intro s hs
      exact List.not_mem_nil
  · simp at hroot

/-- Lookup-tree form of the direct infinite-board soundness theorem. -/
theorem CTree.sound_plane_in {t : CTree} {R C i k : Nat} {g : Xf}
    (hall : t.all (cardOK t.get) = true) (hroot : rootOK t.get R C i g = true)
    (hk : (t.get i).all (fun c => decide (c.h ≤ k)) = true) :
    PlaneBlackWinsIn k [] [] :=
  cards_sound_plane_in (CTree.all_get hall) hroot hk

end Snaky
