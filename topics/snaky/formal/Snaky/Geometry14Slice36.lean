import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice36_eq : slice orient2 8 = part36 := by decide +kernel
theorem part36_length : part36.length = 13 := by decide +kernel
end Snaky.Geometry14
