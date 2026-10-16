import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice40_eq : slice orient4 0 = part40 := by decide +kernel
theorem part40_length : part40.length = 9 := by decide +kernel
end Snaky.Geometry10
