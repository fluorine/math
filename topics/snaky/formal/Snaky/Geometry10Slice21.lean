import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice21_eq : slice orient2 1 = part21 := by decide +kernel
theorem part21_length : part21.length = 9 := by decide +kernel
end Snaky.Geometry10
