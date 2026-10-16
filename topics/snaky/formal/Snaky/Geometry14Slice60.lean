import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice60_eq : slice orient4 4 = part60 := by decide +kernel
theorem part60_length : part60.length = 13 := by decide +kernel
end Snaky.Geometry14
