import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice44_eq : slice orient4 4 = part44 := by decide +kernel
theorem part44_length : part44.length = 9 := by decide +kernel
end Snaky.Geometry10
