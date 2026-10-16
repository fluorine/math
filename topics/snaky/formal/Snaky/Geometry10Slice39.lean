import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice39_eq : slice orient3 9 = part39 := by decide +kernel
theorem part39_length : part39.length = 0 := by decide +kernel
end Snaky.Geometry10
