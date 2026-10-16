import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice74_eq : slice orient7 4 = part74 := by decide +kernel
theorem part74_length : part74.length = 6 := by decide +kernel
end Snaky.Geometry10
