import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice23_eq : slice orient2 3 = part23 := by decide +kernel
theorem part23_length : part23.length = 9 := by decide +kernel
end Snaky.Geometry10
