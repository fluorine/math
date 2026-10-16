import Snaky.Game

/-!
# Finite Breaker safety invariants

The conclusion is about the existing `BlackWins` game, not a second game
semantics. An invariant excludes an immediate target completion and supplies
a legal reply when a reply exists. A continuation may restore the invariant
or use an independently proved safe leaf. Exhaustion is not a Breaker pass.
-/
namespace Snaky.Breaker

def Fresh (N : Nat) (M W : List Nat) (x : Nat) : Prop :=
  x < N ∧ x ∉ M ∧ x ∉ W

def Disjoint (M W : List Nat) : Prop := ∀ x ∈ M, x ∉ W

def Extends (A B : List Nat) : Prop := ∀ x ∈ A, x ∈ B

def NoComplete (P : List (List Nat)) (M : List Nat) : Prop :=
  ∀ e ∈ P, ¬ (∀ x ∈ e, x ∈ M)

def AfterSafe (P : List (List Nat)) (N : Nat)
    (I : List Nat → List Nat → Prop) (M W : List Nat) : Prop :=
  NoComplete P M ∧
  ((∃ w, Fresh N M W w) →
    ∃ w, Fresh N M W w ∧ (I M (w :: W) ∨ ¬ BlackWins P N M (w :: W)))

def InvariantStep (P : List (List Nat)) (N : Nat)
    (I : List Nat → List Nat → Prop) : Prop :=
  ∀ M W, I M W → ∀ u, Fresh N M W u → AfterSafe P N I (u :: M) W

mutual
theorem invariant_not_blackWins {P : List (List Nat)} {N : Nat}
    {I : List Nat → List Nat → Prop} (step : InvariantStep P N I)
    {M W : List Nat} (hI : I M W) : ¬ BlackWins P N M W
  | .move _ _ u hu huM huW h =>
    afterSafe_not_whiteToMoveLoses step (step M W hI u ⟨hu, huM, huW⟩) h

theorem afterSafe_not_whiteToMoveLoses {P : List (List Nat)} {N : Nat}
    {I : List Nat → List Nat → Prop} (step : InvariantStep P N I)
    {M W : List Nat} (hs : AfterSafe P N I M W) : ¬ WhiteToMoveLoses P N M W
  | .won _ _ p hp hsub => hs.1 p hp hsub
  | .reply _ _ hf h =>
    let ⟨w, hw, tail⟩ := hs.2 hf
    match tail with
    | .inl hI => invariant_not_blackWins step hI (h w hw.1 hw.2.1 hw.2.2)
    | .inr hn => hn (h w hw.1 hw.2.1 hw.2.2)
end

theorem extends_cons {A B : List Nat} (h : Extends A B) (x : Nat) :
    Extends A (x :: B) := fun y hy => List.mem_cons_of_mem x (h y hy)

theorem fresh_of_extends {N x : Nat} {M₀ W₀ M W : List Nat}
    (hm : Extends M₀ M) (hw : Extends W₀ W) (h : Fresh N M W x) :
    Fresh N M₀ W₀ x :=
  ⟨h.1, fun hx => h.2.1 (hm x hx), fun hx => h.2.2 (hw x hx)⟩

theorem disjoint_cons_maker {N u : Nat} {M W : List Nat}
    (hd : Disjoint M W) (hu : Fresh N M W u) : Disjoint (u :: M) W := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hu.2.2
  · exact hd x hx

theorem disjoint_cons_breaker {N v : Nat} {M W : List Nat}
    (hd : Disjoint M W) (hv : Fresh N M W v) : Disjoint M (v :: W) := by
  intro x hx hxW
  rcases List.mem_cons.mp hxW with rfl | hxW
  · exact hv.2.1 hx
  · exact hd x hx hxW

theorem fresh_cons_maker {N x u : Nat} {M W : List Nat}
    (hx : Fresh N M W x) (hne : x ≠ u) : Fresh N (u :: M) W x :=
  ⟨hx.1, by simpa only [List.mem_cons, not_or] using And.intro hne hx.2.1, hx.2.2⟩

theorem fresh_cons_both {N x u v : Nat} {M W : List Nat}
    (hx : Fresh N M W x) (hxu : x ≠ u) (hxv : x ≠ v) :
    Fresh N (u :: M) (v :: W) x :=
  ⟨hx.1, by simpa only [List.mem_cons, not_or] using And.intro hxu hx.2.1,
    by simpa only [List.mem_cons, not_or] using And.intro hxv hx.2.2⟩

def TwoFreshCover (P : List (List Nat)) (N : Nat) (M W : List Nat) : Prop :=
  ∀ e ∈ P, (∀ x ∈ e, x ∉ W) →
    ∃ x y, x ∈ e ∧ y ∈ e ∧ x ≠ y ∧ Fresh N M W x ∧ Fresh N M W y

theorem noComplete_after_of_twoFresh {P : List (List Nat)} {N u : Nat}
    {M W : List Nat} (hd : Disjoint M W) (hu : Fresh N M W u)
    (hc : TwoFreshCover P N M W) : NoComplete P (u :: M) := by
  intro e he hsub
  have hd' := disjoint_cons_maker hd hu
  have hlive : ∀ x ∈ e, x ∉ W := fun x hx => hd' x (hsub x hx)
  obtain ⟨x, y, hx, hy, hne, hxf, hyf⟩ := hc e he hlive
  have hxu : x = u := (List.mem_cons.mp (hsub x hx)).resolve_right hxf.2.1
  have hyu : y = u := (List.mem_cons.mp (hsub y hy)).resolve_right hyf.2.1
  exact hne (hxu.trans hyu.symm)

end Snaky.Breaker
