import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice24_eq : slice orient2 4 = part24 := by decide +kernel
theorem part24_length : part24.length = 9 := by decide +kernel
end Snaky.Geometry10
