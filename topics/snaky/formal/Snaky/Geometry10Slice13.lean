import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice13_eq : slice orient1 3 = part13 := by decide +kernel
theorem part13_length : part13.length = 6 := by decide +kernel
end Snaky.Geometry10
