import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice32_eq : slice orient3 2 = part32 := by decide +kernel
theorem part32_length : part32.length = 6 := by decide +kernel
end Snaky.Geometry10
