import Snaky.Geometry10Slice70
import Snaky.Geometry10Slice71
import Snaky.Geometry10Slice72
import Snaky.Geometry10Slice73
import Snaky.Geometry10Slice74
import Snaky.Geometry10Slice75
import Snaky.Geometry10Slice76
import Snaky.Geometry10Slice77
import Snaky.Geometry10Slice78
import Snaky.Geometry10Slice79
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group7_eq : (List.range 10).flatMap (slice orient7) = group7 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice70_eq, slice71_eq, slice72_eq, slice73_eq, slice74_eq, slice75_eq, slice76_eq, slice77_eq, slice78_eq, slice79_eq]
  rfl

end Snaky.Geometry10
