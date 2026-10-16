import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice09_eq : slice orient0 9 = part09 := by decide +kernel
theorem part09_length : part09.length = 13 := by decide +kernel
end Snaky.Geometry14
