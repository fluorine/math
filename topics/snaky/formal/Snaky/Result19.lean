import Snaky.Plane
import Snaky.Gen19.All

/-!
# Snaky in at most nineteen Maker moves

The generated card data are checked by Lean's kernel using the original
ordinary-card rules. The construction algorithm and its Python verifier are
not hypotheses of these theorems. `Snaky.Plane` supplies a direct soundness
argument against every legal Breaker reply on the infinite square board.
-/

namespace Snaky

/-- The accepted root has a budget of at most nineteen Maker claims. -/
theorem Gen19.root_height : (Gen19.getK 3467).all (fun c => decide (c.h ≤ 19)) = true := by
  decide +kernel

/-- From the empty 17 × 17 board, Maker moves first and forces the exact
six-cell Snaky by the nineteenth Maker claim, allowing all D4 placements. -/
theorem snaky_wins_17x17_in_19 :
    BlackWinsIn (placements 17 17 snaky) (17 * 17) 19 [] [] :=
  CTree.sound_in Gen19.tree_ok Gen19.root_ok Gen19.root_height

/-- From the empty infinite square board `Int × Int`, Maker moves first
and forces the exact six-cell Snaky by the nineteenth Maker claim, against
every legal Breaker strategy. Breaker replies are arbitrary integer pairs. -/
theorem snaky_wins_plane_in_19 : PlaneBlackWinsIn 19 [] [] :=
  CTree.sound_plane_in Gen19.tree_ok Gen19.root_ok Gen19.root_height

end Snaky
