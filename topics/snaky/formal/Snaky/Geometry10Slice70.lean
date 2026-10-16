import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice70_eq : slice orient7 0 = part70 := by decide +kernel
theorem part70_length : part70.length = 6 := by decide +kernel
end Snaky.Geometry10
