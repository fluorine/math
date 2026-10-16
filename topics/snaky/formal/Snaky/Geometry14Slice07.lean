import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice07_eq : slice orient0 7 = part07 := by decide +kernel
theorem part07_length : part07.length = 13 := by decide +kernel
end Snaky.Geometry14
