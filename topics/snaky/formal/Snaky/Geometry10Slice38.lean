import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice38_eq : slice orient3 8 = part38 := by decide +kernel
theorem part38_length : part38.length = 6 := by decide +kernel
end Snaky.Geometry10
