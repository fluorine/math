import Snaky.Geometry14Slice98
import Snaky.Geometry14Slice99
import Snaky.Geometry14Slice100
import Snaky.Geometry14Slice101
import Snaky.Geometry14Slice102
import Snaky.Geometry14Slice103
import Snaky.Geometry14Slice104
import Snaky.Geometry14Slice105
import Snaky.Geometry14Slice106
import Snaky.Geometry14Slice107
import Snaky.Geometry14Slice108
import Snaky.Geometry14Slice109
import Snaky.Geometry14Slice110
import Snaky.Geometry14Slice111
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group7_eq : (List.range 14).flatMap (slice orient7) = group7 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice98_eq, slice99_eq, slice100_eq, slice101_eq, slice102_eq, slice103_eq, slice104_eq, slice105_eq, slice106_eq, slice107_eq, slice108_eq, slice109_eq, slice110_eq, slice111_eq]
  rfl

end Snaky.Geometry14
