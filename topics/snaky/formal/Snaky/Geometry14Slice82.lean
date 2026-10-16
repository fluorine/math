import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice82_eq : slice orient5 12 = part82 := by decide +kernel
theorem part82_length : part82.length = 10 := by decide +kernel
end Snaky.Geometry14
