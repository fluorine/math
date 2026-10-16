import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice19_eq : slice orient1 5 = part19 := by decide +kernel
theorem part19_length : part19.length = 10 := by decide +kernel
end Snaky.Geometry14
