import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice26_eq : slice orient2 6 = part26 := by decide +kernel
theorem part26_length : part26.length = 0 := by decide +kernel
end Snaky.Geometry10
