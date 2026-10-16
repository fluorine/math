import Snaky.Geometry10Slice60
import Snaky.Geometry10Slice61
import Snaky.Geometry10Slice62
import Snaky.Geometry10Slice63
import Snaky.Geometry10Slice64
import Snaky.Geometry10Slice65
import Snaky.Geometry10Slice66
import Snaky.Geometry10Slice67
import Snaky.Geometry10Slice68
import Snaky.Geometry10Slice69
import Snaky.Geometry10GroupsData

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group6_eq : (List.range 10).flatMap (slice orient6) = group6 := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice60_eq, slice61_eq, slice62_eq, slice63_eq, slice64_eq, slice65_eq, slice66_eq, slice67_eq, slice68_eq, slice69_eq]
  rfl

end Snaky.Geometry10
