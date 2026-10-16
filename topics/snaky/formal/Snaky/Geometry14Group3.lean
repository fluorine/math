import Snaky.Geometry14Slice42
import Snaky.Geometry14Slice43
import Snaky.Geometry14Slice44
import Snaky.Geometry14Slice45
import Snaky.Geometry14Slice46
import Snaky.Geometry14Slice47
import Snaky.Geometry14Slice48
import Snaky.Geometry14Slice49
import Snaky.Geometry14Slice50
import Snaky.Geometry14Slice51
import Snaky.Geometry14Slice52
import Snaky.Geometry14Slice53
import Snaky.Geometry14Slice54
import Snaky.Geometry14Slice55
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group3_eq : (List.range 14).flatMap (slice orient3) = group3 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice42_eq, slice43_eq, slice44_eq, slice45_eq, slice46_eq, slice47_eq, slice48_eq, slice49_eq, slice50_eq, slice51_eq, slice52_eq, slice53_eq, slice54_eq, slice55_eq]
  rfl

end Snaky.Geometry14
