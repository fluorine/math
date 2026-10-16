import Snaky.Geometry14Slice14
import Snaky.Geometry14Slice15
import Snaky.Geometry14Slice16
import Snaky.Geometry14Slice17
import Snaky.Geometry14Slice18
import Snaky.Geometry14Slice19
import Snaky.Geometry14Slice20
import Snaky.Geometry14Slice21
import Snaky.Geometry14Slice22
import Snaky.Geometry14Slice23
import Snaky.Geometry14Slice24
import Snaky.Geometry14Slice25
import Snaky.Geometry14Slice26
import Snaky.Geometry14Slice27
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group1_eq : (List.range 14).flatMap (slice orient1) = group1 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice14_eq, slice15_eq, slice16_eq, slice17_eq, slice18_eq, slice19_eq, slice20_eq, slice21_eq, slice22_eq, slice23_eq, slice24_eq, slice25_eq, slice26_eq, slice27_eq]
  rfl

end Snaky.Geometry14
