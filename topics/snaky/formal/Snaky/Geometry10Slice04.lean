import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice04_eq : slice orient0 4 = part04 := by decide +kernel
theorem part04_length : part04.length = 9 := by decide +kernel
end Snaky.Geometry10
