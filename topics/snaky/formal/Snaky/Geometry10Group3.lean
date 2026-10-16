import Snaky.Geometry10Slice30
import Snaky.Geometry10Slice31
import Snaky.Geometry10Slice32
import Snaky.Geometry10Slice33
import Snaky.Geometry10Slice34
import Snaky.Geometry10Slice35
import Snaky.Geometry10Slice36
import Snaky.Geometry10Slice37
import Snaky.Geometry10Slice38
import Snaky.Geometry10Slice39
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group3_eq : (List.range 10).flatMap (slice orient3) = group3 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice30_eq, slice31_eq, slice32_eq, slice33_eq, slice34_eq, slice35_eq, slice36_eq, slice37_eq, slice38_eq, slice39_eq]
  rfl

end Snaky.Geometry10
