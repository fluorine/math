import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice43_eq : slice orient3 1 = part43 := by decide +kernel
theorem part43_length : part43.length = 10 := by decide +kernel
end Snaky.Geometry14
