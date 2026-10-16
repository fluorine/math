import Snaky.Geometry14Slice84
import Snaky.Geometry14Slice85
import Snaky.Geometry14Slice86
import Snaky.Geometry14Slice87
import Snaky.Geometry14Slice88
import Snaky.Geometry14Slice89
import Snaky.Geometry14Slice90
import Snaky.Geometry14Slice91
import Snaky.Geometry14Slice92
import Snaky.Geometry14Slice93
import Snaky.Geometry14Slice94
import Snaky.Geometry14Slice95
import Snaky.Geometry14Slice96
import Snaky.Geometry14Slice97
import Snaky.Geometry14GroupsData

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem group6_eq : (List.range 14).flatMap (slice orient6) = group6 := by
  have hr : List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slice84_eq, slice85_eq, slice86_eq, slice87_eq, slice88_eq, slice89_eq, slice90_eq, slice91_eq, slice92_eq, slice93_eq, slice94_eq, slice95_eq, slice96_eq, slice97_eq]
  rfl

end Snaky.Geometry14
