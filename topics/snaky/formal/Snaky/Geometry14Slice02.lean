import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice02_eq : slice orient0 2 = part02 := by decide +kernel
theorem part02_length : part02.length = 13 := by decide +kernel
end Snaky.Geometry14
