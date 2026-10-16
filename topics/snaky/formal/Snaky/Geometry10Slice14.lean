import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice14_eq : slice orient1 4 = part14 := by decide +kernel
theorem part14_length : part14.length = 6 := by decide +kernel
end Snaky.Geometry10
