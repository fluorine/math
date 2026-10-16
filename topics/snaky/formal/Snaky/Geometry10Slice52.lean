import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice52_eq : slice orient5 2 = part52 := by decide +kernel
theorem part52_length : part52.length = 6 := by decide +kernel
end Snaky.Geometry10
