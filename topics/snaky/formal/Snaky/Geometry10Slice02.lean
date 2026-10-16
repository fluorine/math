import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice02_eq : slice orient0 2 = part02 := by decide +kernel
theorem part02_length : part02.length = 9 := by decide +kernel
end Snaky.Geometry10
