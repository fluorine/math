import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice18_eq : slice orient1 4 = part18 := by decide +kernel
theorem part18_length : part18.length = 10 := by decide +kernel
end Snaky.Geometry14
