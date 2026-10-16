import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice85_eq : slice orient6 1 = part85 := by decide +kernel
theorem part85_length : part85.length = 13 := by decide +kernel
end Snaky.Geometry14
