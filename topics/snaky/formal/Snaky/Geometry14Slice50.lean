import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice50_eq : slice orient3 8 = part50 := by decide +kernel
theorem part50_length : part50.length = 10 := by decide +kernel
end Snaky.Geometry14
