import Snaky.Geometry10Slice00
import Snaky.Geometry10Slice01
import Snaky.Geometry10Slice02
import Snaky.Geometry10Slice03
import Snaky.Geometry10Slice04
import Snaky.Geometry10Slice05
import Snaky.Geometry10Slice06
import Snaky.Geometry10Slice07
import Snaky.Geometry10Slice08
import Snaky.Geometry10Slice09
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group0_eq : (List.range 10).flatMap (slice orient0) = group0 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice00_eq, slice01_eq, slice02_eq, slice03_eq, slice04_eq, slice05_eq, slice06_eq, slice07_eq, slice08_eq, slice09_eq]
  rfl

end Snaky.Geometry10
