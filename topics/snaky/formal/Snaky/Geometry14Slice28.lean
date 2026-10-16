import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice28_eq : slice orient2 0 = part28 := by decide +kernel
theorem part28_length : part28.length = 13 := by decide +kernel
end Snaky.Geometry14
