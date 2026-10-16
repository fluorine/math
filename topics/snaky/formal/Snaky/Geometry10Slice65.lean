import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice65_eq : slice orient6 5 = part65 := by decide +kernel
theorem part65_length : part65.length = 9 := by decide +kernel
end Snaky.Geometry10
