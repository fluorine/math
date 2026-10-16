import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice104_eq : slice orient7 6 = part104 := by decide +kernel
theorem part104_length : part104.length = 10 := by decide +kernel
end Snaky.Geometry14
