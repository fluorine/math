import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice30_eq : slice orient2 2 = part30 := by decide +kernel
theorem part30_length : part30.length = 13 := by decide +kernel
end Snaky.Geometry14
