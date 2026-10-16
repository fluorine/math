import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice15_eq : slice orient1 5 = part15 := by decide +kernel
theorem part15_length : part15.length = 6 := by decide +kernel
end Snaky.Geometry10
