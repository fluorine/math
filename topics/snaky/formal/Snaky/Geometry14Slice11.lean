import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice11_eq : slice orient0 11 = part11 := by decide +kernel
theorem part11_length : part11.length = 0 := by decide +kernel
end Snaky.Geometry14
