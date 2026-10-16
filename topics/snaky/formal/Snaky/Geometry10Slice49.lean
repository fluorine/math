import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice49_eq : slice orient4 9 = part49 := by decide +kernel
theorem part49_length : part49.length = 0 := by decide +kernel
end Snaky.Geometry10
