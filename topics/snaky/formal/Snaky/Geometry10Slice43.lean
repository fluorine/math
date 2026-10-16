import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice43_eq : slice orient4 3 = part43 := by decide +kernel
theorem part43_length : part43.length = 9 := by decide +kernel
end Snaky.Geometry10
