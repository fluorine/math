import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice30_eq : slice orient3 0 = part30 := by decide +kernel
theorem part30_length : part30.length = 6 := by decide +kernel
end Snaky.Geometry10
