import Snaky.GenMakerCloseout.Check
import Snaky.MakerCloseoutPlaced
import Snaky.MakerCloseoutCounts

/-!
# Conditional continuation on the actual 14 by 14 board

The root is used after Maker's claim (12,6) and one actual Breaker reply.
Its eight required stones are not an empty-board opening. The exact N30
and N31 old colors are retained, including every stone outside the card.
The sixteen exceptional initial replies remain outside this theorem.
-/

namespace Snaky.MakerCloseout

/-- The general conditional theorem; all later physical replies are included. -/
theorem continuation_wins_in_eight {M W : List Nat}
    (h : Placed 14 14 continuation frame M W) :
    BlackWinsIn (placements 14 14 snaky) 196 8 M W := by
  exact sound_aux (CTree.all_get GenMakerCloseout.tree_ok) 14 14 8 continuation
    ⟨25, rfl⟩ (by decide +kernel) frame (by decide +kernel) M W h

/-- Exact applicability for every legal physical reply. -/
theorem n30_exact_partition (b : Fin 196)
    (hM : b.val ∉ initialClaim :: n30Maker) (_hW : b.val ∉ n30Breaker) :
    Placed 14 14 continuation frame (initialClaim :: n30Maker) (b.val :: n30Breaker) ↔
      b.val ∉ exceptions :=
  ⟨placed_avoids_exceptions, placed_after_reply n30_initial_facts b.val hM⟩

theorem n31_exact_partition (b : Fin 196)
    (hM : b.val ∉ initialClaim :: n31Maker) (_hW : b.val ∉ n31Breaker) :
    Placed 14 14 continuation frame (initialClaim :: n31Maker) (b.val :: n31Breaker) ↔
      b.val ∉ exceptions :=
  ⟨placed_avoids_exceptions, placed_after_reply n31_initial_facts b.val hM⟩

/-- N30: eight further Maker claims after q and any nonexceptional actual reply. -/
theorem n30_after_q_wins (b : Fin 196)
    (hM : b.val ∉ initialClaim :: n30Maker) (hW : b.val ∉ n30Breaker)
    (hE : b.val ∉ exceptions) :
    BlackWinsIn (placements 14 14 snaky) 196 8
      (initialClaim :: n30Maker) (b.val :: n30Breaker) :=
  continuation_wins_in_eight ((n30_exact_partition b hM hW).2 hE)

/-- N31: the same continuation retains the additional old Maker and Breaker stones. -/
theorem n31_after_q_wins (b : Fin 196)
    (hM : b.val ∉ initialClaim :: n31Maker) (hW : b.val ∉ n31Breaker)
    (hE : b.val ∉ exceptions) :
    BlackWinsIn (placements 14 14 snaky) 196 8
      (initialClaim :: n31Maker) (b.val :: n31Breaker) :=
  continuation_wins_in_eight ((n31_exact_partition b hM hW).2 hE)

end Snaky.MakerCloseout
