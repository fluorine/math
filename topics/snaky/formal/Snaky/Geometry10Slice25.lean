import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice25_eq : slice orient2 5 = part25 := by decide +kernel
theorem part25_length : part25.length = 9 := by decide +kernel
end Snaky.Geometry10
