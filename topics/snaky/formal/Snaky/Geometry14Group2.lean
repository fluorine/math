import Snaky.Geometry14Slice28
import Snaky.Geometry14Slice29
import Snaky.Geometry14Slice30
import Snaky.Geometry14Slice31
import Snaky.Geometry14Slice32
import Snaky.Geometry14Slice33
import Snaky.Geometry14Slice34
import Snaky.Geometry14Slice35
import Snaky.Geometry14Slice36
import Snaky.Geometry14Slice37
import Snaky.Geometry14Slice38
import Snaky.Geometry14Slice39
import Snaky.Geometry14Slice40
import Snaky.Geometry14Slice41
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group2_eq : (List.range 14).flatMap (slice orient2) = group2 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice28_eq, slice29_eq, slice30_eq, slice31_eq, slice32_eq, slice33_eq, slice34_eq, slice35_eq, slice36_eq, slice37_eq, slice38_eq, slice39_eq, slice40_eq, slice41_eq]
  rfl

end Snaky.Geometry14
