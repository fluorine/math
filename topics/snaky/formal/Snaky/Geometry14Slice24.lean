import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice24_eq : slice orient1 10 = part24 := by decide +kernel
theorem part24_length : part24.length = 10 := by decide +kernel
end Snaky.Geometry14
