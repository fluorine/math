import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice10_eq : slice orient1 0 = part10 := by decide +kernel
theorem part10_length : part10.length = 6 := by decide +kernel
end Snaky.Geometry10
