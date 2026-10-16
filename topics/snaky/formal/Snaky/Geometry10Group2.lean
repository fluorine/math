import Snaky.Geometry10Slice20
import Snaky.Geometry10Slice21
import Snaky.Geometry10Slice22
import Snaky.Geometry10Slice23
import Snaky.Geometry10Slice24
import Snaky.Geometry10Slice25
import Snaky.Geometry10Slice26
import Snaky.Geometry10Slice27
import Snaky.Geometry10Slice28
import Snaky.Geometry10Slice29
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group2_eq : (List.range 10).flatMap (slice orient2) = group2 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice20_eq, slice21_eq, slice22_eq, slice23_eq, slice24_eq, slice25_eq, slice26_eq, slice27_eq, slice28_eq, slice29_eq]
  rfl

end Snaky.Geometry10
