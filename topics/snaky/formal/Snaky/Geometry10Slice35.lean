import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice35_eq : slice orient3 5 = part35 := by decide +kernel
theorem part35_length : part35.length = 6 := by decide +kernel
end Snaky.Geometry10
