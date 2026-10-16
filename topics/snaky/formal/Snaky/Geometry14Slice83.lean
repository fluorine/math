import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice83_eq : slice orient5 13 = part83 := by decide +kernel
theorem part83_length : part83.length = 0 := by decide +kernel
end Snaky.Geometry14
