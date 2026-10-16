import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice47_eq : slice orient4 7 = part47 := by decide +kernel
theorem part47_length : part47.length = 0 := by decide +kernel
end Snaky.Geometry10
