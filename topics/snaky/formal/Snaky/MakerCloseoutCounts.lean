import Snaky.MakerCloseoutState
import Snaky.MakerCloseoutCountN30Legal
import Snaky.MakerCloseoutCountN30Covered
import Snaky.MakerCloseoutCountN30Remaining
import Snaky.MakerCloseoutCountN31Legal
import Snaky.MakerCloseoutCountN31Covered
import Snaky.MakerCloseoutCountN31Remaining

namespace Snaky.MakerCloseout

def physicalState (n : Nat) (M W : List Nat) : Prop :=
  M.length = n ∧ W.length = n ∧ M.Nodup ∧ W.Nodup ∧
  (∀ x ∈ M, x < 196 ∧ x ∉ W) ∧ (∀ x ∈ W, x < 196) ∧
  initialClaim < 196 ∧ initialClaim ∉ M ∧ initialClaim ∉ W

theorem n30_full_state : physicalState 30 n30Maker n30Breaker := by
  unfold physicalState
  decide +kernel

theorem n31_full_state : physicalState 31 n31Maker n31Breaker := by
  unfold physicalState
  decide +kernel

theorem initial_reply_counts :
    (legalReplies n30Maker n30Breaker).length = 135 ∧
    (coveredReplies n30Maker n30Breaker).length = 119 ∧
    (remainingReplies n30Maker n30Breaker).length = 16 ∧
    (legalReplies n31Maker n31Breaker).length = 133 ∧
    (coveredReplies n31Maker n31Breaker).length = 117 ∧
    (remainingReplies n31Maker n31Breaker).length = 16 ∧
    exceptions.length = 16 ∧ exceptions.Nodup := by
  exact ⟨n30_legal_count, n30_covered_count, n30_remaining_count,
    n31_legal_count, n31_covered_count, n31_remaining_count, rfl, by decide +kernel⟩

private theorem legal_mem (M W : List Nat) (b : Nat) :
    b ∈ legalReplies M W ↔ b < 196 ∧ b ∉ initialClaim :: M ∧ b ∉ W := by
  simp [legalReplies, List.mem_filter, List.contains_iff_mem, and_assoc]

private theorem exceptions_fresh :
    (∀ b ∈ exceptions, b < 196 ∧ b ∉ initialClaim :: n30Maker ∧ b ∉ n30Breaker) ∧
    (∀ b ∈ exceptions, b < 196 ∧ b ∉ initialClaim :: n31Maker ∧ b ∉ n31Breaker) := by
  decide +kernel

theorem exceptions_legal :
    (∀ b ∈ exceptions, b ∈ legalReplies n30Maker n30Breaker) ∧
    (∀ b ∈ exceptions, b ∈ legalReplies n31Maker n31Breaker) := by
  exact ⟨fun b hb => (legal_mem _ _ _).2 (exceptions_fresh.1 b hb),
    fun b hb => (legal_mem _ _ _).2 (exceptions_fresh.2 b hb)⟩

private theorem covered_mem (M W : List Nat) (b : Nat) :
    b ∈ coveredReplies M W ↔ b ∈ legalReplies M W ∧ b ∉ exceptions := by
  simp [coveredReplies, List.mem_filter, List.contains_iff_mem]

private theorem remaining_mem (M W : List Nat) (b : Nat) :
    b ∈ remainingReplies M W ↔ b ∈ legalReplies M W ∧ b ∈ exceptions := by
  simp [remainingReplies, List.mem_filter, List.contains_iff_mem]

private theorem partition_at (M W : List Nat)
    (h : ∀ b ∈ exceptions, b ∈ legalReplies M W) (b : Nat) :
    (b ∈ remainingReplies M W ↔ b ∈ exceptions) ∧
    (b ∈ legalReplies M W ↔ b ∈ coveredReplies M W ∨ b ∈ exceptions) := by
  rw [remaining_mem, covered_mem]
  constructor
  · exact ⟨fun hb => hb.2, fun hb => ⟨h b hb, hb⟩⟩
  · constructor
    · intro hb
      by_cases he : b ∈ exceptions
      · exact Or.inr he
      · exact Or.inl ⟨hb, he⟩
    · intro hb
      rcases hb with ⟨hl, _⟩ | he
      · exact hl
      · exact h b he

/-- Exact complete partition of all physical initial replies at both parents. -/
theorem initial_reply_partition (b : Fin 196) :
    (b.val ∈ remainingReplies n30Maker n30Breaker ↔ b.val ∈ exceptions) ∧
    (b.val ∈ remainingReplies n31Maker n31Breaker ↔ b.val ∈ exceptions) ∧
    (b.val ∈ legalReplies n30Maker n30Breaker ↔
      b.val ∈ coveredReplies n30Maker n30Breaker ∨ b.val ∈ exceptions) ∧
    (b.val ∈ legalReplies n31Maker n31Breaker ↔
      b.val ∈ coveredReplies n31Maker n31Breaker ∨ b.val ∈ exceptions) := by
  have h30 := partition_at n30Maker n30Breaker exceptions_legal.1 b.val
  have h31 := partition_at n31Maker n31Breaker exceptions_legal.2 b.val
  exact ⟨h30.1, h31.1, h30.2, h31.2⟩

end Snaky.MakerCloseout
