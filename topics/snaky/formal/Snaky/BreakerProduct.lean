import Snaky.BreakerSafety

/-!
# Disjoint ordinary component defenses

Each component is an actual negative theorem for its selected local targets,
with cells outside its domain blocked in the local game. Physical Maker
ownership inside that domain equals virtual Maker ownership; virtual Breaker
ownership inside it is included in physical Breaker ownership. An already
physically blocked virtual reply permits a real fresh filler. Outside moves
stutter. Immediate wins and the last Maker claim are checked before replying.

This is a semantic product theorem. The initial local defenses and literal
coverage remain separate proof obligations; no external verifier is trusted.
-/
namespace Snaky.Breaker

def outside (N : Nat) (D : List Nat) : List Nat :=
  (List.range N).filter (fun x => decide (x ∉ D))

def LocalRealizes (N : Nat) (D VM VB M W : List Nat) : Prop :=
  (∀ x ∈ D, x ∈ VM ↔ x ∈ M) ∧
  (∀ x ∈ D, x ∈ VB → x ∈ W) ∧
  (∀ x, x < N → x ∉ D → x ∈ VB)

def LocalGood (P : List (List Nat)) (N : Nat) (D VM VB M W : List Nat) : Prop :=
  LocalRealizes N D VM VB M W ∧ NoComplete P VM ∧ ¬ BlackWins P N VM VB

theorem local_fresh {N u : Nat} {D VM VB M W : List Nat}
    (h : LocalRealizes N D VM VB M W) (huD : u ∈ D) (hu : Fresh N M W u) :
    Fresh N VM VB u :=
  ⟨hu.1, fun hm => hu.2.1 ((h.1 u huD).1 hm), fun hb => hu.2.2 (h.2.1 u huD hb)⟩

theorem local_reply_inside {N w : Nat} {D VM VB M W : List Nat}
    (h : LocalRealizes N D VM VB M W) (hw : Fresh N VM VB w) : w ∈ D := by
  by_cases hin : w ∈ D
  · exact hin
  · exact False.elim (hw.2.2 (h.2.2 w hw.1 hin))

theorem local_stutter {N u v : Nat} {D VM VB M W : List Nat}
    (h : LocalRealizes N D VM VB M W) (hu : u ∉ D) :
    LocalRealizes N D VM VB (u :: M) (v :: W) := by
  refine ⟨?_, ?_, h.2.2⟩
  · intro x hx
    constructor
    · intro hm
      exact List.mem_cons_of_mem _ ((h.1 x hx).1 hm)
    · intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact False.elim (hu hx)
      · exact (h.1 x hx).2 hm
  · intro x hx hb
    exact List.mem_cons_of_mem _ (h.2.1 x hx hb)

theorem local_maker_step {N u v : Nat} {D VM VB M W : List Nat}
    (h : LocalRealizes N D VM VB M W) :
    LocalRealizes N D (u :: VM) VB (u :: M) (v :: W) := by
  refine ⟨?_, ?_, h.2.2⟩
  · intro x hx
    simp only [List.mem_cons]
    exact or_congr Iff.rfl (h.1 x hx)
  · intro x hx hb
    exact List.mem_cons_of_mem _ (h.2.1 x hx hb)

theorem local_both_step {N u v w : Nat} {D VM VB M W : List Nat}
    (h : LocalRealizes N D VM VB M W) (hw : w ∈ v :: W) :
    LocalRealizes N D (u :: VM) (w :: VB) (u :: M) (v :: W) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (local_maker_step (u := u) (v := v) h).1
  · intro x hx hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hw
    · exact List.mem_cons_of_mem _ (h.2.1 x hx hb)
  · intro x hx hn
    exact List.mem_cons_of_mem _ (h.2.2 x hx hn)

/-- Extract the next safe virtual state from the ordinary finite game. -/
theorem local_safe_step {P : List (List Nat)} {N u : Nat} {VM VB : List Nat}
    (hn : ¬ BlackWins P N VM VB) (hu : Fresh N VM VB u) :
    NoComplete P (u :: VM) ∧
      (¬ BlackWins P N (u :: VM) VB ∨
       ∃ w, Fresh N (u :: VM) VB w ∧ ¬ BlackWins P N (u :: VM) (w :: VB)) := by
  classical
  have hw : ¬ WhiteToMoveLoses P N (u :: VM) VB :=
    fun h => hn (.move VM VB u hu.1 hu.2.1 hu.2.2 h)
  refine ⟨fun e he hsub => hw (.won _ _ e he hsub), ?_⟩
  by_cases hf : ∃ w, Fresh N (u :: VM) VB w
  · right
    apply Classical.byContradiction
    intro hh
    apply hw
    refine .reply _ _ hf ?_
    intro w hN hM hB
    apply Classical.byContradiction
    intro hwin
    exact hh ⟨w, ⟨hN,hM,hB⟩, hwin⟩
  · left
    intro h
    cases h with
    | move _ _ w hN hM hB _ => exact hf ⟨w, hN, hM, hB⟩

def ProductState (N k : Nat) (M₀ W₀ : List Nat)
    (domains : Nat → List Nat) (targets : Nat → List (List Nat))
    (M W : List Nat) : Prop :=
  Extends M₀ M ∧ Extends W₀ W ∧ Disjoint M W ∧
    ∀ i ∈ List.range k, ∃ VM VB, LocalGood (targets i) N (domains i) VM VB M W

def DomainsDisjoint (k : Nat) (domains : Nat → List Nat) : Prop :=
  ∀ i ∈ List.range k, ∀ j ∈ List.range k, i ≠ j →
    ∀ x ∈ domains i, x ∉ domains j

def ProductCovers (P : List (List Nat)) (W₀ : List Nat) (k : Nat)
    (targets : Nat → List (List Nat)) : Prop :=
  ∀ e ∈ P, (∀ x ∈ e, x ∉ W₀) →
    ∃ i ∈ List.range k, ∃ g ∈ targets i, ∀ x ∈ g, x ∈ e

theorem product_noComplete_after {P : List (List Nat)} {N k u : Nat}
    {M₀ W₀ M W : List Nat} {domains : Nat → List Nat}
    {targets : Nat → List (List Nat)}
    (within : ∀ i ∈ List.range k, ∀ g ∈ targets i, ∀ x ∈ g, x ∈ domains i)
    (cover : ProductCovers P W₀ k targets)
    (hs : ProductState N k M₀ W₀ domains targets M W) (hu : Fresh N M W u) :
    NoComplete P (u :: M) := by
  intro e he hsub
  have hd := disjoint_cons_maker hs.2.2.1 hu
  have live : ∀ x ∈ e, x ∉ W₀ := fun x hx hB => hd x (hsub x hx) (hs.2.1 x hB)
  obtain ⟨i, hi, g, hg, hge⟩ := cover e he live
  obtain ⟨VM,VB,hr,hno,hn⟩ := hs.2.2.2 i hi
  by_cases huD : u ∈ domains i
  · have hn' := (local_safe_step hn (local_fresh hr huD hu)).1
    apply hn' g hg
    intro x hx
    rcases List.mem_cons.mp (hsub x (hge x hx)) with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((hr.1 x (within i hi g hg x hx)).2 hm)
  · apply hno g hg
    intro x hx
    rcases List.mem_cons.mp (hsub x (hge x hx)) with rfl | hm
    · exact False.elim (huD (within i hi g hg x hx))
    · exact (hr.1 x (within i hi g hg x hx)).2 hm

theorem product_update_one {N k i u v : Nat} {M₀ W₀ M W VM VB : List Nat}
    {domains : Nat → List Nat} {targets : Nat → List (List Nat)}
    (disj : DomainsDisjoint k domains)
    (hs : ProductState N k M₀ W₀ domains targets M W)
    (hi : i ∈ List.range k) (huD : u ∈ domains i)
    (hu : Fresh N M W u) (hv : Fresh N (u :: M) W v)
    (next : LocalGood (targets i) N (domains i) VM VB (u :: M) (v :: W)) :
    ProductState N k M₀ W₀ domains targets (u :: M) (v :: W) := by
  refine ⟨extends_cons hs.1 u, extends_cons hs.2.1 v,
    disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact ⟨VM,VB,next⟩
  · obtain ⟨VMj,VBj,hr,hn,hb⟩ := hs.2.2.2 j hj
    exact ⟨VMj,VBj,local_stutter hr (disj i hi j hj (Ne.symm hji) u huD),hn,hb⟩

/-- Disjoint, independently defended ordinary components protect all targets
that contain one of their guards. Extra physical Breaker insertions are allowed. -/
theorem product_not_blackWins {P : List (List Nat)} {N k : Nat} {M₀ W₀ : List Nat}
    {domains : Nat → List Nat} {targets : Nat → List (List Nat)}
    (hd : Disjoint M₀ W₀)
    (fresh : ∀ i ∈ List.range k, ∀ x ∈ domains i, Fresh N M₀ W₀ x)
    (disj : DomainsDisjoint k domains)
    (within : ∀ i ∈ List.range k, ∀ g ∈ targets i, ∀ x ∈ g, x ∈ domains i)
    (safe : ∀ i ∈ List.range k, NoComplete (targets i) [])
    (defend : ∀ i ∈ List.range k,
      ¬ BlackWins (targets i) N [] (outside N (domains i)))
    (cover : ProductCovers P W₀ k targets) : ¬ BlackWins P N M₀ W₀ := by
  classical
  let I := ProductState N k M₀ W₀ domains targets
  have step : InvariantStep P N I := by
    intro M W hs u hu
    refine ⟨product_noComplete_after within cover hs hu, ?_⟩
    intro hfree
    by_cases active : ∃ i ∈ List.range k, u ∈ domains i
    · obtain ⟨i,hi,huD⟩ := active
      obtain ⟨VM,VB,hr,hno,hn⟩ := hs.2.2.2 i hi
      obtain ⟨hno',next⟩ := local_safe_step hn (local_fresh hr huD hu)
      rcases next with hn' | ⟨w,hw,hn'⟩
      · obtain ⟨v,hv⟩ := hfree
        exact ⟨v,hv,Or.inl (product_update_one disj hs hi huD hu hv
          ⟨local_maker_step hr,hno',hn'⟩)⟩
      · have hwD := local_reply_inside (local_maker_step (u := u) (v := w) hr) hw
        by_cases hwW : w ∈ W
        · obtain ⟨v,hv⟩ := hfree
          exact ⟨v,hv,Or.inl (product_update_one disj hs hi huD hu hv
            ⟨local_both_step hr (List.mem_cons_of_mem v hwW),hno',hn'⟩)⟩
        · have hwM : w ∉ u :: M := by
            intro hm
            have hr' := local_maker_step (u := u) (v := w) hr
            exact hw.2.1 ((hr'.1 w hwD).2 hm)
          have hv : Fresh N (u :: M) W w := ⟨hw.1,hwM,hwW⟩
          exact ⟨w,hv,Or.inl (product_update_one disj hs hi huD hu hv
            ⟨local_both_step hr List.mem_cons_self,hno',hn'⟩)⟩
    · obtain ⟨v,hv⟩ := hfree
      refine ⟨v,hv,Or.inl ⟨extends_cons hs.1 u,extends_cons hs.2.1 v,
        disjoint_cons_breaker (disjoint_cons_maker hs.2.2.1 hu) hv,?_⟩⟩
      intro i hi
      obtain ⟨VM,VB,hr,hno,hn⟩ := hs.2.2.2 i hi
      exact ⟨VM,VB,local_stutter hr (fun h => active ⟨i,hi,h⟩),hno,hn⟩
  apply invariant_not_blackWins step
  refine ⟨fun _ h => h,fun _ h => h,hd,?_⟩
  intro i hi
  refine ⟨[],outside N (domains i),?_,safe i hi,defend i hi⟩
  refine ⟨?_,?_,?_⟩
  · intro x hx
    constructor
    · intro h
      cases h
    · intro hm
      exact False.elim ((fresh i hi x hx).2.1 hm)
  · intro x hx hb
    have hn : x ∉ domains i := by simpa only [outside,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact False.elim (hn hx)
  · intro x hN hn
    simp only [outside,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨hN,hn⟩

end Snaky.Breaker
