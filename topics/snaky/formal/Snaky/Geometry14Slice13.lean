import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice13_eq : slice orient0 13 = part13 := by decide +kernel
theorem part13_length : part13.length = 0 := by decide +kernel
end Snaky.Geometry14
