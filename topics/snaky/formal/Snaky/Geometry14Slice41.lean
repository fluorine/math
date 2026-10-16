import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice41_eq : slice orient2 13 = part41 := by decide +kernel
theorem part41_length : part41.length = 0 := by decide +kernel
end Snaky.Geometry14
