import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice40_eq : slice orient2 12 = part40 := by decide +kernel
theorem part40_length : part40.length = 0 := by decide +kernel
end Snaky.Geometry14
