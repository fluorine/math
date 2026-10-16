import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice33_eq : slice orient2 5 = part33 := by decide +kernel
theorem part33_length : part33.length = 13 := by decide +kernel
end Snaky.Geometry14
