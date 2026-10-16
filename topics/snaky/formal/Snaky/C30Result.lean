import Snaky.C30Checks

/-!
The target of this theorem is the explicitly selected 17-guard game. Twelve
guards omit additional cells of their physical Snaky witnesses. Accordingly,
this is not a Maker win on the physical 10 by 10 Snaky board. The theorem does
retain the exact nine initial stones of each color and all physical replies.
-/

namespace Snaky.C30Selected
open SelectedAttack

theorem core_fits : ∀ x ∈ core, x < 100 := by decide +kernel
theorem guards_in_core : ∀ p ∈ guards, ∀ x ∈ p, x ∈ core := by decide +kernel
theorem initial_trace : Trace core row0.maker row0.breaker initialMaker initialBreaker := by
  unfold Trace
  decide +kernel

theorem selected_contract :
    guards.length = 17 ∧ core.length = 22 ∧ core.Nodup ∧
    initialMaker.length = 9 ∧ initialBreaker.length = 9 ∧
    initialMaker.Nodup ∧ initialBreaker.Nodup ∧
    (∀ x ∈ initialMaker, x < 100 ∧ x ∉ initialBreaker ∧ x ∉ core) ∧
    (∀ x ∈ initialBreaker, x < 100 ∧ x ∉ core) := by
  decide +kernel

/-- All legal physical Breaker replies are covered, for the selected guards only. -/
theorem selected_guards_win_in_ten :
    BlackWinsIn guards 100 10 initialMaker initialBreaker :=
  sound (Tree.all_get tree_ok) core_fits guards_in_core 10 row0
    ⟨0, rfl⟩ (by decide +kernel) initialMaker initialBreaker initial_trace

theorem selected_guards_win : BlackWins guards 100 initialMaker initialBreaker :=
  selected_guards_win_in_ten.toBlackWins

end Snaky.C30Selected
