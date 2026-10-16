import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice22_eq : slice orient1 8 = part22 := by decide +kernel
theorem part22_length : part22.length = 10 := by decide +kernel
end Snaky.Geometry14
