import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice33_eq : slice orient3 3 = part33 := by decide +kernel
theorem part33_length : part33.length = 6 := by decide +kernel
end Snaky.Geometry10
