import Snaky.BreakerPartial
import Snaky.BreakerProduct
import Snaky.BreakerSwitch

/-! Small ordinary components that commit to a partial matching after their
first actual entry. These local game theorems are suitable inputs to the
semantic product theorem; fillers and interleavings are handled there. -/
namespace Snaky.Breaker

theorem fresh_outside {N x : Nat} {D : List Nat} (hx : x ∈ D) (hN : x < N) :
    Fresh N [] (outside N D) x := by
  refine ⟨hN, List.not_mem_nil, ?_⟩
  intro hb
  have hn : x ∉ D := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp hb).2
  exact hn hx

theorem outside_fresh_inside {N x : Nat} {D : List Nat}
    (hx : Fresh N [] (outside N D) x) : x ∈ D := by
  by_cases hin : x ∈ D
  · exact hin
  · apply False.elim
    apply hx.2.2
    simp only [outside,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨hx.1,hin⟩

theorem guard_noComplete_empty {R : List Nat} {P : List (List Nat)}
    (h : GuardOK R P) : NoComplete P [] := by
  intro g hg hsub
  obtain ⟨x,hx,_,_,_⟩ := (h g hg).2
  exact List.not_mem_nil (hsub x hx)

theorem guard_noComplete_singleton {R : List Nat} {P : List (List Nat)}
    (h : GuardOK R P) (u : Nat) : NoComplete P [u] := by
  intro g hg hsub
  obtain ⟨x,hx,y,hy,hxy⟩ := (h g hg).2
  exact hxy ((List.mem_singleton.mp (hsub x hx)).trans
    (List.mem_singleton.mp (hsub y hy)).symm)

def LocalReplyOK (P : List (List Nat)) (N : Nat) (D : List Nat)
    (reply : Nat → Nat) (localDomain : Nat → List Nat)
    (localMate : Nat → Nat → Nat) : Prop :=
  ∀ u ∈ D,
    Fresh N [u] (outside N D) (reply u) ∧
    PartialOK N [u] (reply u :: outside N D) (localDomain u) (localMate u) ∧
    PartialCovers P [u] (reply u :: outside N D) (localDomain u) (localMate u)

theorem local_reply_not_blackWins {P : List (List Nat)} {N : Nat} {D : List Nat}
    {reply : Nat → Nat} {localDomain : Nat → List Nat} {localMate : Nat → Nat → Nat}
    (shape : GuardOK D P) (rows : LocalReplyOK P N D reply localDomain localMate) :
    ¬ BlackWins P N [] (outside N D) := by
  intro h
  cases h with
  | move _ _ u hN hM hB hwhite =>
    have hu : Fresh N [] (outside N D) u := ⟨hN,hM,hB⟩
    obtain ⟨hv,hpairs,hcover⟩ := rows u (outside_fresh_inside hu)
    have hd : Disjoint [u] (outside N D) :=
      disjoint_cons_maker (fun _ h => False.elim (List.not_mem_nil h)) hu
    cases hwhite with
    | won _ _ e he hsub => exact guard_noComplete_singleton shape u e he hsub
    | reply _ _ _ h =>
      exact partial_matching_not_blackWins (disjoint_cons_breaker hd hv) hpairs hcover
        (h (reply u) hv.1 hv.2.1 hv.2.2)

theorem pair_component_not_blackWins {N a b : Nat} (ha : a < N) (hb : b < N)
    (hne : a ≠ b) : ¬ BlackWins [[a,b]] N [] (outside N [a,b]) := by
  let mate := fun x => if x = a then b else a
  have hok : PartialOK N [] (outside N [a,b]) [a,b] mate := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · refine ⟨fresh_outside (by simp) ha, ?_⟩
      simp [mate,hne,Ne.symm hne]
    · refine ⟨fresh_outside (by simp) hb, ?_⟩
      simp [mate,hne,Ne.symm hne]
  have hcover : PartialCovers [[a,b]] [] (outside N [a,b]) [a,b] mate := by
    intro e he _
    have he' : e = [a,b] := List.mem_singleton.mp he
    subst e
    exact ⟨a,by simp,by simp,by simp [mate]⟩
  exact partial_matching_not_blackWins (fun _ h => False.elim (List.not_mem_nil h)) hok hcover

end Snaky.Breaker
