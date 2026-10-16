import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice16_eq : slice orient1 6 = part16 := by decide +kernel
theorem part16_length : part16.length = 6 := by decide +kernel
end Snaky.Geometry10
