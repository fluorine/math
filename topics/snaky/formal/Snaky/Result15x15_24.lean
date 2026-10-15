import Snaky.Gen15x15_24.All

/-!
# Snaky on the 15 × 15 board within twenty-four Maker moves

This target uses the unchanged ordinary-card semantics and finite-board
soundness theorem. The generated card obligations must all be reduced by the
Lean kernel; the construction algorithm is not a hypothesis of the result.
The build status is recorded separately in `RESULT-15X15-24.md`.
-/

namespace Snaky

/-- The compact root has a budget of at most twenty-four Maker claims. -/
theorem Gen15x15_24.root_height :
    (Gen15x15_24.getK 8733).all (fun c => decide (c.h ≤ 24)) = true := by
  decide +kernel

/-- From the empty 15 × 15 board, Maker moves first and forces the exact
six-cell Snaky by the twenty-fourth Maker claim, allowing all D4 placements. -/
theorem snaky_wins_15x15_in_24 :
    BlackWinsIn (placements 15 15 snaky) (15 * 15) 24 [] [] :=
  CTree.sound_in Gen15x15_24.tree_ok Gen15x15_24.root_ok Gen15x15_24.root_height

end Snaky
