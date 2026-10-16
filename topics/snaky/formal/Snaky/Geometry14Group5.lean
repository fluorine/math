import Snaky.Geometry14Slice70
import Snaky.Geometry14Slice71
import Snaky.Geometry14Slice72
import Snaky.Geometry14Slice73
import Snaky.Geometry14Slice74
import Snaky.Geometry14Slice75
import Snaky.Geometry14Slice76
import Snaky.Geometry14Slice77
import Snaky.Geometry14Slice78
import Snaky.Geometry14Slice79
import Snaky.Geometry14Slice80
import Snaky.Geometry14Slice81
import Snaky.Geometry14Slice82
import Snaky.Geometry14Slice83
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group5_eq : (List.range 14).flatMap (slice orient5) = group5 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice70_eq, slice71_eq, slice72_eq, slice73_eq, slice74_eq, slice75_eq, slice76_eq, slice77_eq, slice78_eq, slice79_eq, slice80_eq, slice81_eq, slice82_eq, slice83_eq]
  rfl

end Snaky.Geometry14
