import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice14_eq : slice orient1 0 = part14 := by decide +kernel
theorem part14_length : part14.length = 10 := by decide +kernel
end Snaky.Geometry14
