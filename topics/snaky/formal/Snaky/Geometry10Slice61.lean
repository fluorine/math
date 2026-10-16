import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice61_eq : slice orient6 1 = part61 := by decide +kernel
theorem part61_length : part61.length = 9 := by decide +kernel
end Snaky.Geometry10
