import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice75_eq : slice orient7 5 = part75 := by decide +kernel
theorem part75_length : part75.length = 6 := by decide +kernel
end Snaky.Geometry10
