import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice62_eq : slice orient4 6 = part62 := by decide +kernel
theorem part62_length : part62.length = 13 := by decide +kernel
end Snaky.Geometry14
