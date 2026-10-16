import Snaky.BreakerSwitch

/-!
# Complete conditional physical P52 defense

The exact Maker-turn state is 11+11 on the full 10×10 board. The finite
checks below use the repository's original `placements` geometry. The
strategy is a total exterior matching followed by one six-cell switch.
No Python verifier, browser claim or unchecked source strategy is an axiom.
This theorem does not settle P53, S9, or the empty board.
-/
namespace Snaky.P52
open Snaky.Breaker

def maker : List Nat := [32,37,43,44,45,46,47,57,67,75,84]
def breaker : List Nat := [33,34,36,38,52,55,56,58,74,77,94]
def reserved : List Nat := [16,17,18,26,27,28]
def guards : List (List Nat) := [[16,17],[16,26,27],[17,18,27],[18,27,28]]

def outsidePairs : List (Nat × Nat) :=
  [(3,4),(5,6),(7,8),(10,20),(11,21),(12,22),(13,14),(15,25),
   (23,24),(29,49),(30,40),(31,42),(41,50),(51,61),(53,54),(59,79),
   (60,80),(62,72),(63,73),(64,65),(66,76),(68,78),(70,71),(81,91),
   (82,83),(85,86),(88,89),(92,93),(95,96),
   (0,1),(2,9),(19,35),(39,48),(69,87),(90,97),(98,99)]

def outsideMate : Nat → Nat := mateOfPairs outsidePairs

def reply : Nat → Nat
  | 16 => 17
  | 17 => 16
  | 18 => 27
  | 26 => 27
  | 27 => 17
  | 28 => 27
  | u => u

def localPairs : Nat → List (Nat × Nat)
  | 16 => [(26,27),(18,28)]
  | 17 => [(18,27),(26,28)]
  | 18 => [(16,17),(26,28)]
  | 26 => [(16,17),(18,28)]
  | 27 => [(16,26),(18,28)]
  | 28 => [(16,17),(18,26)]
  | _ => []

def localMate (u : Nat) : Nat → Nat := mateOfPairs (localPairs u)

theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel

theorem reserved_fresh : ∀ x ∈ reserved, Fresh 100 maker breaker x := by
  unfold Fresh
  decide +kernel

theorem exterior_matching : OuterOK 100 maker breaker reserved outsideMate := by
  unfold OuterOK Fresh
  decide +kernel

theorem guard_shape : GuardOK reserved guards := by
  unfold GuardOK
  decide +kernel

theorem switch_rows : SwitchOK reserved guards reply localMate := by
  unfold SwitchOK
  decide +kernel

/-! Small corruption controls: a missing exterior mate and a self-reply fail. -/
theorem missing_pair_rejected :
    ¬ OuterOK 100 maker breaker reserved
      (mateOfPairs (outsidePairs.filter (fun p => p != (0,1)))) := by
  unfold OuterOK Fresh
  decide +kernel

theorem self_reply_rejected :
    ¬ SwitchOK reserved guards (fun u => if u = 16 then 16 else reply u) localMate := by
  unfold SwitchOK
  decide +kernel

end Snaky.P52
