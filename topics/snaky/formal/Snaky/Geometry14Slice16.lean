import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice16_eq : slice orient1 2 = part16 := by decide +kernel
theorem part16_length : part16.length = 10 := by decide +kernel
end Snaky.Geometry14
