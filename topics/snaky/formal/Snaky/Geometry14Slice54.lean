import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice54_eq : slice orient3 12 = part54 := by decide +kernel
theorem part54_length : part54.length = 10 := by decide +kernel
end Snaky.Geometry14
