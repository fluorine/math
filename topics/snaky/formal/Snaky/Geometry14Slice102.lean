import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice102_eq : slice orient7 4 = part102 := by decide +kernel
theorem part102_length : part102.length = 10 := by decide +kernel
end Snaky.Geometry14
