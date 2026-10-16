import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice25_eq : slice orient1 11 = part25 := by decide +kernel
theorem part25_length : part25.length = 10 := by decide +kernel
end Snaky.Geometry14
