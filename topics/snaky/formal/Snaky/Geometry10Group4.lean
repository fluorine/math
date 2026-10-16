import Snaky.Geometry10Slice40
import Snaky.Geometry10Slice41
import Snaky.Geometry10Slice42
import Snaky.Geometry10Slice43
import Snaky.Geometry10Slice44
import Snaky.Geometry10Slice45
import Snaky.Geometry10Slice46
import Snaky.Geometry10Slice47
import Snaky.Geometry10Slice48
import Snaky.Geometry10Slice49
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group4_eq : (List.range 10).flatMap (slice orient4) = group4 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice40_eq, slice41_eq, slice42_eq, slice43_eq, slice44_eq, slice45_eq, slice46_eq, slice47_eq, slice48_eq, slice49_eq]
  rfl

end Snaky.Geometry10
