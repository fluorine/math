import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice20_eq : slice orient1 6 = part20 := by decide +kernel
theorem part20_length : part20.length = 10 := by decide +kernel
end Snaky.Geometry14
