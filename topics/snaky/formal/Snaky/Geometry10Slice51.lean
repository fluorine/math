import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice51_eq : slice orient5 1 = part51 := by decide +kernel
theorem part51_length : part51.length = 6 := by decide +kernel
end Snaky.Geometry10
