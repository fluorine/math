import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice84_eq : slice orient6 0 = part84 := by decide +kernel
theorem part84_length : part84.length = 13 := by decide +kernel
end Snaky.Geometry14
