import Snaky.P52Data

/-! Exact continued P52/P53 endpoint data, separate from the original P52 state.
The same pristine six-cell switch is reused. Literal values are untrusted
until their finite hypotheses and full-board coverage are kernel checked. -/
namespace Snaky.P52Continued
open Snaky.Breaker

def commonPairs : List (Nat × Nat) :=
  [(1,3),(4,5),(6,19),(7,8),(13,14),(15,25),(21,23),
   (29,49),(30,40),(59,79),(60,80),(62,72),(64,65),(81,91),
   (82,83),(85,86),(88,89),(92,93),(95,96)]

namespace Endpoint52
def maker : List Nat :=
  [22,32,37,42,43,44,45,46,47,53,57,63,67,75,76,78,84]
def breaker : List Nat :=
  [12,31,33,34,36,38,52,54,55,56,58,66,68,73,74,77,94]
def outsidePairs : List (Nat × Nat) := commonPairs ++
  [(41,50),(51,61),(70,71),(0,2),(9,10),(11,20),(24,35),
   (39,48),(69,87),(90,97),(98,99)]
def outsideMate := mateOfPairs outsidePairs
theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel
theorem reserved_fresh : ∀ x ∈ P52.reserved, Fresh 100 maker breaker x := by
  unfold Fresh
  decide +kernel
theorem exterior_matching : OuterOK 100 maker breaker P52.reserved outsideMate := by
  unfold OuterOK Fresh
  decide +kernel
end Endpoint52

namespace Endpoint53
def maker : List Nat :=
  [22,32,37,41,42,43,44,45,46,47,51,57,61,67,75,76,78,84]
def breaker : List Nat :=
  [12,31,33,34,36,38,50,52,53,55,56,58,66,68,71,74,77,94]
def outsidePairs : List (Nat × Nat) := commonPairs ++
  [(63,73),(0,2),(9,10),(11,20),(24,35),(39,48),(54,69),
   (70,87),(90,97),(98,99)]
def outsideMate := mateOfPairs outsidePairs
theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel
theorem reserved_fresh : ∀ x ∈ P52.reserved, Fresh 100 maker breaker x := by
  unfold Fresh
  decide +kernel
theorem exterior_matching : OuterOK 100 maker breaker P52.reserved outsideMate := by
  unfold OuterOK Fresh
  decide +kernel
end Endpoint53

end Snaky.P52Continued
