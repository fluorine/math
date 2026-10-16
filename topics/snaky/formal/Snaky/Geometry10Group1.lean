import Snaky.Geometry10Slice10
import Snaky.Geometry10Slice11
import Snaky.Geometry10Slice12
import Snaky.Geometry10Slice13
import Snaky.Geometry10Slice14
import Snaky.Geometry10Slice15
import Snaky.Geometry10Slice16
import Snaky.Geometry10Slice17
import Snaky.Geometry10Slice18
import Snaky.Geometry10Slice19
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group1_eq : (List.range 10).flatMap (slice orient1) = group1 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice10_eq, slice11_eq, slice12_eq, slice13_eq, slice14_eq, slice15_eq, slice16_eq, slice17_eq, slice18_eq, slice19_eq]
  rfl

end Snaky.Geometry10
