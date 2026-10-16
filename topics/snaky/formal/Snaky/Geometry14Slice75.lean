import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice75_eq : slice orient5 5 = part75 := by decide +kernel
theorem part75_length : part75.length = 10 := by decide +kernel
end Snaky.Geometry14
