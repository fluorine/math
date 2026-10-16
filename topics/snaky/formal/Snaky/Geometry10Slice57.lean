import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice57_eq : slice orient5 7 = part57 := by decide +kernel
theorem part57_length : part57.length = 6 := by decide +kernel
end Snaky.Geometry10
