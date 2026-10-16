import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice06_eq : slice orient0 6 = part06 := by decide +kernel
theorem part06_length : part06.length = 0 := by decide +kernel
end Snaky.Geometry10
