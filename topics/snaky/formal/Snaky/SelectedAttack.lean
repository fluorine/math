import Snaky.Bounded

/-!
A finite selected-target attack checker. The certificate tracks only the cells
in `K`, but its soundness theorem quantifies over every legal physical reply.
An outside reply leaves the tracked Breaker set unchanged. Every nonterminal
row must exhibit a free cell in `K`, so board exhaustion cannot create a win.
This proves the game for the supplied target family, not for a larger shape.
-/

namespace Snaky.SelectedAttack

inductive Step where
  | finish (cell : Nat)
  | next (row : Nat)
deriving DecidableEq, Repr

structure Row where
  maker : List Nat
  breaker : List Nat
  height : Nat
  move : Nat
  outside : Step
  replies : List (Nat × Step)
deriving DecidableEq, Repr

def choose (replies : List (Nat × Step)) (w : Nat) : Step :=
  match replies with
  | [] => .finish 0
  | (v, action) :: tail => if w = v then action else choose tail w

def Hit (P : List (List Nat)) (M : List Nat) : Prop :=
  ∃ p ∈ P, ∀ x ∈ p, x ∈ M

instance (P : List (List Nat)) (M : List Nat) : Decidable (Hit P M) := by
  unfold Hit
  infer_instance

def StepOK (P : List (List Nat)) (K : List Nat) (get : Nat → Option Row)
    (h : Nat) (M W : List Nat) : Step → Prop
  | .finish x => 1 < h ∧ x ∈ K ∧ x ∉ M ∧ x ∉ W ∧ Hit P (x :: M)
  | .next i => match get i with
    | none => False
    | some c => c.height < h ∧ c.maker = M ∧ c.breaker = W

instance (P : List (List Nat)) (K : List Nat) (get : Nat → Option Row)
    (h : Nat) (M W : List Nat) (s : Step) : Decidable (StepOK P K get h M W s) := by
  cases s with
  | finish x => unfold StepOK; infer_instance
  | next i =>
    change Decidable (match get i with
      | none => False
      | some c => c.height < h ∧ c.maker = M ∧ c.breaker = W)
    cases get i <;> infer_instance

def Valid (P : List (List Nat)) (K : List Nat) (get : Nat → Option Row) (r : Row) : Prop :=
  0 < r.height ∧ r.move ∈ K ∧ r.move ∉ r.maker ∧ r.move ∉ r.breaker ∧
  (Hit P (r.move :: r.maker) ∨
    ((∃ w ∈ K, w ∉ r.move :: r.maker ∧ w ∉ r.breaker) ∧
      StepOK P K get r.height (r.move :: r.maker) r.breaker r.outside ∧
      ∀ w ∈ K, w ∉ r.move :: r.maker → w ∉ r.breaker →
        StepOK P K get r.height (r.move :: r.maker) (w :: r.breaker)
          (choose r.replies w)))

instance (P : List (List Nat)) (K : List Nat) (get : Nat → Option Row) (r : Row) :
    Decidable (Valid P K get r) := by
  unfold Valid
  infer_instance

inductive Tree where
  | leaf (i : Nat) (row : Row)
  | node (split : Nat) (left right : Tree)

def Tree.get : Tree → Nat → Option Row
  | .leaf i r, j => if j = i then some r else none
  | .node m left right, j => if j < m then left.get j else right.get j

def Tree.All (p : Row → Prop) : Tree → Prop
  | .leaf _ r => p r
  | .node _ left right => left.All p ∧ right.All p

theorem Tree.all_get {p : Row → Prop} :
    ∀ {t : Tree}, t.All p → ∀ i r, t.get i = some r → p r
  | .leaf j c, h, i, r, hi => by
    simp only [Tree.get] at hi
    split at hi
    · cases hi; exact h
    · contradiction
  | .node m left right, h, i, r, hi => by
    simp only [Tree.get] at hi
    split at hi
    · exact Tree.all_get h.1 i r hi
    · exact Tree.all_get h.2 i r hi

/-- Exact membership on the selected domain; all other old colors are retained. -/
def Trace (K A B M W : List Nat) : Prop :=
  (∀ x ∈ K, x ∈ A ↔ x ∈ M) ∧ (∀ x ∈ K, x ∈ B ↔ x ∈ W)

private theorem trace_maker {K A B M W : List Nat} (h : Trace K A B M W) (p : Nat) :
    Trace K (p :: A) B (p :: M) W := by
  refine ⟨?_, h.2⟩
  intro x hx
  simpa only [List.mem_cons] using or_congr (Iff.rfl (a := x = p)) (h.1 x hx)

private theorem trace_inside {K A B M W : List Nat} (h : Trace K A B M W) (w : Nat) :
    Trace K A (w :: B) M (w :: W) := by
  refine ⟨h.1, ?_⟩
  intro x hx
  simpa only [List.mem_cons] using or_congr (Iff.rfl (a := x = w)) (h.2 x hx)

private theorem trace_outside {K A B M W : List Nat} (h : Trace K A B M W)
    {w : Nat} (hw : w ∉ K) : Trace K A B M (w :: W) := by
  refine ⟨h.1, ?_⟩
  intro x hx
  have hn : x ≠ w := fun e => hw (e ▸ hx)
  simpa only [List.mem_cons, hn, false_or] using h.2 x hx

private theorem hit_real {P : List (List Nat)} {K A B M W : List Nat}
    (hP : ∀ p ∈ P, ∀ x ∈ p, x ∈ K) (h : Trace K A B M W) (hh : Hit P A) : Hit P M := by
  obtain ⟨p, hp, hsub⟩ := hh
  exact ⟨p, hp, fun x hx => (h.1 x (hP p hp x hx)).1 (hsub x hx)⟩

private theorem step_sound {P : List (List Nat)} {K : List Nat} {N : Nat}
    {get : Nat → Option Row} {n h : Nat}
    (hK : ∀ x ∈ K, x < N) (hP : ∀ p ∈ P, ∀ x ∈ p, x ∈ K)
    (ih : ∀ c, (∃ i, get i = some c) → c.height ≤ n →
      ∀ M W, Trace K c.maker c.breaker M W → BlackWinsIn P N n M W)
    {A B M W : List Nat} (ht : Trace K A B M W) (hh : h ≤ n + 1)
    {s : Step} (hs : StepOK P K get h A B s) : BlackWinsIn P N n M W := by
  cases s with
  | finish x =>
    obtain ⟨h2, hxK, hxA, hxB, hhit⟩ := hs
    cases n with
    | zero => omega
    | succ n =>
      have hxM : x ∉ M := fun hx => hxA ((ht.1 x hxK).2 hx)
      have hxW : x ∉ W := fun hx => hxB ((ht.2 x hxK).2 hx)
      obtain ⟨p, hp, hsub⟩ := hit_real hP (trace_maker ht x) hhit
      exact .move n M W x (hK x hxK) hxM hxW (.won n _ _ p hp hsub)
  | next i =>
    unfold StepOK at hs
    cases hc : get i with
    | none => simp [hc] at hs
    | some c =>
      have hs' : c.height < h ∧ c.maker = A ∧ c.breaker = B := by
        simpa only [hc] using hs
      obtain ⟨hlt, hA, hB⟩ := hs'
      exact ih c ⟨i, hc⟩ (by omega) M W (by simpa only [hA, hB] using ht)

/-- A checked finite controller yields the actual all-reply bounded game. -/
theorem sound {P : List (List Nat)} {K : List Nat} {N : Nat}
    {get : Nat → Option Row}
    (hall : ∀ i r, get i = some r → Valid P K get r)
    (hK : ∀ x ∈ K, x < N) (hP : ∀ p ∈ P, ∀ x ∈ p, x ∈ K) :
    ∀ n r, (∃ i, get i = some r) → r.height ≤ n →
      ∀ M W, Trace K r.maker r.breaker M W → BlackWinsIn P N n M W := by
  intro n
  induction n with
  | zero =>
    intro r hr hh M W ht
    obtain ⟨i, hi⟩ := hr
    have hpos := (hall i r hi).1
    omega
  | succ n ih =>
    intro r hr hh M W ht
    obtain ⟨i, hi⟩ := hr
    obtain ⟨hpos, hpK, hpA, hpB, hnext⟩ := hall i r hi
    have hpM : r.move ∉ M := fun hp => hpA ((ht.1 r.move hpK).2 hp)
    have hpW : r.move ∉ W := fun hp => hpB ((ht.2 r.move hpK).2 hp)
    apply BlackWinsIn.move n M W r.move (hK r.move hpK) hpM hpW
    have htM := trace_maker ht r.move
    rcases hnext with hhit | ⟨hfree, hout, hins⟩
    · obtain ⟨p, hp, hsub⟩ := hit_real hP htM hhit
      exact .won n _ _ p hp hsub
    · obtain ⟨v, hvK, hvA, hvB⟩ := hfree
      refine .reply n _ _ ⟨v, hK v hvK,
        (fun hv => hvA ((htM.1 v hvK).2 hv)),
        (fun hv => hvB ((htM.2 v hvK).2 hv))⟩ ?_
      intro w hw hwM hwW
      by_cases hwK : w ∈ K
      · exact step_sound hK hP ih (trace_inside htM w) hh
          (hins w hwK (fun hm => hwM ((htM.1 w hwK).1 hm))
            (fun hb => hwW ((htM.2 w hwK).1 hb)))
      · exact step_sound hK hP ih (trace_outside htM hwK) hh hout

end Snaky.SelectedAttack
