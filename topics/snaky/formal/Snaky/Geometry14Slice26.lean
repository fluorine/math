import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice26_eq : slice orient1 12 = part26 := by decide +kernel
theorem part26_length : part26.length = 10 := by decide +kernel
end Snaky.Geometry14
