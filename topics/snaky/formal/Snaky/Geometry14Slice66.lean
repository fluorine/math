import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice66_eq : slice orient4 10 = part66 := by decide +kernel
theorem part66_length : part66.length = 0 := by decide +kernel
end Snaky.Geometry14
