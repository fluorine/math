import Snaky.Geometry14Slice00
import Snaky.Geometry14Slice01
import Snaky.Geometry14Slice02
import Snaky.Geometry14Slice03
import Snaky.Geometry14Slice04
import Snaky.Geometry14Slice05
import Snaky.Geometry14Slice06
import Snaky.Geometry14Slice07
import Snaky.Geometry14Slice08
import Snaky.Geometry14Slice09
import Snaky.Geometry14Slice10
import Snaky.Geometry14Slice11
import Snaky.Geometry14Slice12
import Snaky.Geometry14Slice13
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group0_eq : (List.range 14).flatMap (slice orient0) = group0 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice00_eq, slice01_eq, slice02_eq, slice03_eq, slice04_eq, slice05_eq, slice06_eq, slice07_eq, slice08_eq, slice09_eq, slice10_eq, slice11_eq, slice12_eq, slice13_eq]
  rfl

end Snaky.Geometry14
