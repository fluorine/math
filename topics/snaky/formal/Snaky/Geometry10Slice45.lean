import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice45_eq : slice orient4 5 = part45 := by decide +kernel
theorem part45_length : part45.length = 9 := by decide +kernel
end Snaky.Geometry10
