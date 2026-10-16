import Snaky.Geometry14Slice56
import Snaky.Geometry14Slice57
import Snaky.Geometry14Slice58
import Snaky.Geometry14Slice59
import Snaky.Geometry14Slice60
import Snaky.Geometry14Slice61
import Snaky.Geometry14Slice62
import Snaky.Geometry14Slice63
import Snaky.Geometry14Slice64
import Snaky.Geometry14Slice65
import Snaky.Geometry14Slice66
import Snaky.Geometry14Slice67
import Snaky.Geometry14Slice68
import Snaky.Geometry14Slice69
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group4_eq : (List.range 14).flatMap (slice orient4) = group4 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice56_eq, slice57_eq, slice58_eq, slice59_eq, slice60_eq, slice61_eq, slice62_eq, slice63_eq, slice64_eq, slice65_eq, slice66_eq, slice67_eq, slice68_eq, slice69_eq]
  rfl

end Snaky.Geometry14
