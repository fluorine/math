import Snaky.BreakerComponent

namespace Snaky.Breaker

/-- One ordinary round, with safety checked before Breaker's response. -/
theorem one_round_not_blackWins {P : List (List Nat)} {N : Nat} {M W : List Nat}
    (safe : ∀ u, Fresh N M W u → NoComplete P (u :: M))
    (step : ∀ u, Fresh N M W u →
      ∃ v, Fresh N (u :: M) W v ∧ ¬ BlackWins P N (u :: M) (v :: W)) :
    ¬ BlackWins P N M W := by
  intro h
  cases h with
  | move _ _ u hN hM hW hwhite =>
    have hu : Fresh N M W u := ⟨hN,hM,hW⟩
    cases hwhite with
    | won _ _ e he hsub => exact safe u hu e he hsub
    | reply _ _ _ h =>
      obtain ⟨v,hv,hn⟩ := step u hu
      exact hn (h v hv.1 hv.2.1 hv.2.2)

/-- A complete first-entry table for a reserved local game. Each row may
install any already-proved ordinary continuation, including a disjoint
product of smaller pristine components. -/
theorem local_round_not_blackWins {P : List (List Nat)} {N : Nat} {D : List Nat}
    (shape : GuardOK D P)
    (rows : ∀ u ∈ D, ∃ v, Fresh N [u] (outside N D) v ∧
      ¬ BlackWins P N [u] (v :: outside N D)) :
    ¬ BlackWins P N [] (outside N D) := by
  apply one_round_not_blackWins
  · intro u _
    exact guard_noComplete_singleton shape u
  · intro u hu
    exact rows u (outside_fresh_inside hu)

end Snaky.Breaker
