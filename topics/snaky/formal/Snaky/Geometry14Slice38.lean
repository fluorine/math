import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice38_eq : slice orient2 10 = part38 := by decide +kernel
theorem part38_length : part38.length = 0 := by decide +kernel
end Snaky.Geometry14
