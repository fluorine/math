import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice110_eq : slice orient7 12 = part110 := by decide +kernel
theorem part110_length : part110.length = 10 := by decide +kernel
end Snaky.Geometry14
