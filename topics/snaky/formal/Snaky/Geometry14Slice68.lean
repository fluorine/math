import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice68_eq : slice orient4 12 = part68 := by decide +kernel
theorem part68_length : part68.length = 0 := by decide +kernel
end Snaky.Geometry14
