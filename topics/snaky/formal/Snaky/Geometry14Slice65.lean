import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice65_eq : slice orient4 9 = part65 := by decide +kernel
theorem part65_length : part65.length = 13 := by decide +kernel
end Snaky.Geometry14
