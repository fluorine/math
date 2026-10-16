import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice53_eq : slice orient3 11 = part53 := by decide +kernel
theorem part53_length : part53.length = 10 := by decide +kernel
end Snaky.Geometry14
