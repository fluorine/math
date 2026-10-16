import Snaky.GenMakerOpening.All
import Snaky.MakerOpeningPlaced66
import Snaky.MakerOpeningPlaced710

/-! Two conditional openings on the actual 14 by 14 board. Stored one-based
coordinates (7,7), (6,6), (7,10) encode as 90, 75, 132. These are positions
after one claim by each player, not an empty-board theorem. Heights count
further Maker claims and include every subsequent legal physical reply. -/
namespace Snaky.MakerOpening

theorem opening_66_wins_in_nineteen :
    BlackWinsIn (placements 14 14 snaky) 196 19 [90] [75] := by
  exact sound_aux (CTree.all_get GenMakerOpening.tree_ok) 14 14 19 opening66
    ⟨1598, rfl⟩ (by decide +kernel) frame66 (by decide +kernel) [90] [75]
    opening66_placed

theorem opening_710_wins_in_fifteen :
    BlackWinsIn (placements 14 14 snaky) 196 15 [90] [132] := by
  exact sound_aux (CTree.all_get GenMakerOpening.tree_ok) 14 14 15 opening710
    ⟨1646, rfl⟩ (by decide +kernel) frame710 (by decide +kernel) [90] [132]
    opening710_placed

theorem opening_coordinates :
    idx 14 (6, 6) = 90 ∧ idx 14 (5, 5) = 75 ∧ idx 14 (6, 9) = 132 := by
  decide +kernel

end Snaky.MakerOpening
