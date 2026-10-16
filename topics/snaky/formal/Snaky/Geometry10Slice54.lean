import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice54_eq : slice orient5 4 = part54 := by decide +kernel
theorem part54_length : part54.length = 6 := by decide +kernel
end Snaky.Geometry10
