import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice62_eq : slice orient6 2 = part62 := by decide +kernel
theorem part62_length : part62.length = 9 := by decide +kernel
end Snaky.Geometry10
