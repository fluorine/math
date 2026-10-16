import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice36_eq : slice orient3 6 = part36 := by decide +kernel
theorem part36_length : part36.length = 6 := by decide +kernel
end Snaky.Geometry10
