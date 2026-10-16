import Snaky.GenMakerCloseout.Data
import Snaky.MakerCloseoutState

namespace Snaky.MakerCloseout

def continuation : Card := GenMakerCloseout.c25

theorem continuation_interface :
    continuation.h = 8 ∧ continuation.p = (11, 6) ∧
    continuation.A.length = 8 ∧ continuation.S.length = 24 := by decide +kernel

/-- Finite facts about the already-owned cells and the safe support, before the reply. -/
def initialFacts (M W : List Nat) : Prop :=
  (∀ a ∈ continuation.A, onBoard 14 14 (frame.app a) ∧ cell a ∈ initialClaim :: M) ∧
  (∀ s ∈ continuation.S, onBoard 14 14 (frame.app s) ∧ cell s ∉ W ∧
    (cell s ∈ initialClaim :: M ∨ cell s ∈ exceptions)) ∧
  (initialClaim :: M).length + (0 :: W).length + 2 * continuation.h ≤ 196

theorem n30_initial_facts : initialFacts n30Maker n30Breaker := by
  unfold initialFacts
  decide +kernel

theorem n31_initial_facts : initialFacts n31Maker n31Breaker := by
  unfold initialFacts
  decide +kernel

theorem exception_in_support : ∀ s ∈ exceptionCoords, s ∈ continuation.S := by
  decide +kernel

theorem placed_after_reply {M W : List Nat} (h : initialFacts M W) (b : Nat)
    (hM : b ∉ initialClaim :: M) (hE : b ∉ exceptions) :
    Placed 14 14 continuation frame (initialClaim :: M) (b :: W) := by
  obtain ⟨hA, hS, hlen⟩ := h
  refine ⟨hA, ?_, ?_⟩
  · intro s hs
    obtain ⟨hon, hW, hcover⟩ := hS s hs
    refine ⟨hon, ?_⟩
    change cell s ∉ b :: W
    simp only [List.mem_cons, not_or]
    refine ⟨?_, hW⟩
    intro heq
    rcases hcover with hm | he
    · exact hM (heq ▸ hm)
    · exact hE (heq ▸ he)
  · simpa only [List.length_append, List.length_cons] using hlen

theorem placed_avoids_exceptions {M W : List Nat} {b : Nat}
    (h : Placed 14 14 continuation frame M (b :: W)) : b ∉ exceptions := by
  intro hb
  rw [exception_coordinate_encoding] at hb
  obtain ⟨s, hs, heq⟩ := List.mem_map.mp hb
  have hfree := (h.2.1 s (exception_in_support s hs)).2
  apply hfree
  change cell s ∈ b :: W
  exact List.mem_cons.mpr (Or.inl heq)

end Snaky.MakerCloseout
