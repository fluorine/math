import Snaky.BreakerSwitch

/-! Coverage composition keeps finite kernel reductions small. -/
namespace Snaky.Breaker

theorem waitingCovers_append {A B : List (List Nat)} {N : Nat}
    {M W R : List Nat} {guards : List (List Nat)} {mate : Nat → Nat}
    (ha : WaitingCovers A N M W R guards mate)
    (hb : WaitingCovers B N M W R guards mate) :
    WaitingCovers (A ++ B) N M W R guards mate := by
  intro e he hlive
  rcases List.mem_append.mp he with he | he
  · exact ha e he hlive
  · exact hb e he hlive

theorem matchingCovers_append {A B : List (List Nat)} {N : Nat}
    {M W : List Nat} {mate : Nat → Nat}
    (ha : MatchingCovers A N M W mate) (hb : MatchingCovers B N M W mate) :
    MatchingCovers (A ++ B) N M W mate := by
  intro e he hlive
  rcases List.mem_append.mp he with he | he
  · exact ha e he hlive
  · exact hb e he hlive

end Snaky.Breaker
