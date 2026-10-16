import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice21_eq : slice orient1 7 = part21 := by decide +kernel
theorem part21_length : part21.length = 10 := by decide +kernel
end Snaky.Geometry14
