import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice52_eq : slice orient3 10 = part52 := by decide +kernel
theorem part52_length : part52.length = 10 := by decide +kernel
end Snaky.Geometry14
