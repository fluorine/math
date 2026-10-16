import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice60_eq : slice orient6 0 = part60 := by decide +kernel
theorem part60_length : part60.length = 9 := by decide +kernel
end Snaky.Geometry10
