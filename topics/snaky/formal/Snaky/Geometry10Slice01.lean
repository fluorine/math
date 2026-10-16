import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice01_eq : slice orient0 1 = part01 := by decide +kernel
theorem part01_length : part01.length = 9 := by decide +kernel
end Snaky.Geometry10
