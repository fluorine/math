import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice41_eq : slice orient4 1 = part41 := by decide +kernel
theorem part41_length : part41.length = 9 := by decide +kernel
end Snaky.Geometry10
