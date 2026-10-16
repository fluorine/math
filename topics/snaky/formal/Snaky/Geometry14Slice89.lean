import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice89_eq : slice orient6 5 = part89 := by decide +kernel
theorem part89_length : part89.length = 13 := by decide +kernel
end Snaky.Geometry14
