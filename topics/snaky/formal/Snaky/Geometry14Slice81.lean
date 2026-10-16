import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice81_eq : slice orient5 11 = part81 := by decide +kernel
theorem part81_length : part81.length = 10 := by decide +kernel
end Snaky.Geometry14
