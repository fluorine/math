import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice100_eq : slice orient7 2 = part100 := by decide +kernel
theorem part100_length : part100.length = 10 := by decide +kernel
end Snaky.Geometry14
