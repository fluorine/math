import Snaky.Geometry10Slice50
import Snaky.Geometry10Slice51
import Snaky.Geometry10Slice52
import Snaky.Geometry10Slice53
import Snaky.Geometry10Slice54
import Snaky.Geometry10Slice55
import Snaky.Geometry10Slice56
import Snaky.Geometry10Slice57
import Snaky.Geometry10Slice58
import Snaky.Geometry10Slice59
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group5_eq : (List.range 10).flatMap (slice orient5) = group5 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice50_eq, slice51_eq, slice52_eq, slice53_eq, slice54_eq, slice55_eq, slice56_eq, slice57_eq, slice58_eq, slice59_eq]
  rfl

end Snaky.Geometry10
