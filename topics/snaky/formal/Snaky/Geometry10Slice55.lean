import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice55_eq : slice orient5 5 = part55 := by decide +kernel
theorem part55_length : part55.length = 6 := by decide +kernel
end Snaky.Geometry10
