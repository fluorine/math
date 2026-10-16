import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice45_eq : slice orient3 3 = part45 := by decide +kernel
theorem part45_length : part45.length = 10 := by decide +kernel
end Snaky.Geometry14
