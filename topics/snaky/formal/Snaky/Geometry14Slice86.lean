import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice86_eq : slice orient6 2 = part86 := by decide +kernel
theorem part86_length : part86.length = 13 := by decide +kernel
end Snaky.Geometry14
