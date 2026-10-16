import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice18_eq : slice orient1 8 = part18 := by decide +kernel
theorem part18_length : part18.length = 6 := by decide +kernel
end Snaky.Geometry10
