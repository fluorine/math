import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice101_eq : slice orient7 3 = part101 := by decide +kernel
theorem part101_length : part101.length = 10 := by decide +kernel
end Snaky.Geometry14
