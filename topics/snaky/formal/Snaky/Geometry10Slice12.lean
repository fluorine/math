import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice12_eq : slice orient1 2 = part12 := by decide +kernel
theorem part12_length : part12.length = 6 := by decide +kernel
end Snaky.Geometry10
