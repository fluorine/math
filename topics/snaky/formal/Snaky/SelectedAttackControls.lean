import Snaky.SelectedAttack

namespace Snaky.SelectedAttack.Controls

def targets : List (List Nat) := [[0, 1], [1, 2]]
def domain : List Nat := [0, 1, 2]
def row : Row := ⟨[], [], 2, 1, .finish 0, [(0, .finish 2), (2, .finish 0)]⟩
def get : Nat → Option Row := (Tree.leaf 0 row).get

theorem valid_domino : Valid targets domain get row := by
  unfold Valid
  decide +kernel

theorem missing_reply_rejected :
    ¬ Valid targets domain get { row with replies := [(2, .finish 0)] } := by
  unfold Valid
  decide +kernel

theorem occupied_completion_rejected :
    ¬ Valid targets domain get { row with outside := .finish 1 } := by
  unfold Valid
  decide +kernel

theorem inadequate_height_rejected :
    ¬ Valid targets domain get { row with height := 1 } := by
  unfold Valid
  decide +kernel

theorem no_free_nonwinning_reply_rejected :
    ¬ Valid [[0, 1]] [0] get ⟨[], [], 1, 0, .finish 1, []⟩ := by
  unfold Valid
  decide +kernel

theorem domino_wins : BlackWinsIn targets 3 2 [] [] :=
  sound (Tree.all_get (t := Tree.leaf 0 row) valid_domino)
    (by decide +kernel) (by decide +kernel)
    2 row ⟨0, rfl⟩ (by decide +kernel) [] [] (by unfold Trace; decide +kernel)

end Snaky.SelectedAttack.Controls
