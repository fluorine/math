import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice53_eq : slice orient5 3 = part53 := by decide +kernel
theorem part53_length : part53.length = 6 := by decide +kernel
end Snaky.Geometry10
