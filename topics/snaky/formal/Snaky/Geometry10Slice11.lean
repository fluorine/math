import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice11_eq : slice orient1 1 = part11 := by decide +kernel
theorem part11_length : part11.length = 6 := by decide +kernel
end Snaky.Geometry10
