import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice70_eq : slice orient5 0 = part70 := by decide +kernel
theorem part70_length : part70.length = 10 := by decide +kernel
end Snaky.Geometry14
