import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice29_eq : slice orient2 9 = part29 := by decide +kernel
theorem part29_length : part29.length = 0 := by decide +kernel
end Snaky.Geometry10
