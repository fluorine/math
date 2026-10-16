import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice28_eq : slice orient2 8 = part28 := by decide +kernel
theorem part28_length : part28.length = 0 := by decide +kernel
end Snaky.Geometry10
