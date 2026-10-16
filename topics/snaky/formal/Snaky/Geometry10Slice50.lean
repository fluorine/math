import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice50_eq : slice orient5 0 = part50 := by decide +kernel
theorem part50_length : part50.length = 6 := by decide +kernel
end Snaky.Geometry10
