import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice03_eq : slice orient0 3 = part03 := by decide +kernel
theorem part03_length : part03.length = 9 := by decide +kernel
end Snaky.Geometry10
