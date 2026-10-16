import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice46_eq : slice orient4 6 = part46 := by decide +kernel
theorem part46_length : part46.length = 0 := by decide +kernel
end Snaky.Geometry10
