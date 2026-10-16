import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice35_eq : slice orient2 7 = part35 := by decide +kernel
theorem part35_length : part35.length = 13 := by decide +kernel
end Snaky.Geometry14
