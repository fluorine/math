import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice06_eq : slice orient0 6 = part06 := by decide +kernel
theorem part06_length : part06.length = 13 := by decide +kernel
end Snaky.Geometry14
