import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice56_eq : slice orient5 6 = part56 := by decide +kernel
theorem part56_length : part56.length = 6 := by decide +kernel
end Snaky.Geometry10
