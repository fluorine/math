import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice08_eq : slice orient0 8 = part08 := by decide +kernel
theorem part08_length : part08.length = 0 := by decide +kernel
end Snaky.Geometry10
