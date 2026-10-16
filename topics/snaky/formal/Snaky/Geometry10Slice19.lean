import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice19_eq : slice orient1 9 = part19 := by decide +kernel
theorem part19_length : part19.length = 0 := by decide +kernel
end Snaky.Geometry10
