import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice48_eq : slice orient4 8 = part48 := by decide +kernel
theorem part48_length : part48.length = 0 := by decide +kernel
end Snaky.Geometry10
