import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice64_eq : slice orient4 8 = part64 := by decide +kernel
theorem part64_length : part64.length = 13 := by decide +kernel
end Snaky.Geometry14
