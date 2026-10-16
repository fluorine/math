import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice01_eq : slice orient0 1 = part01 := by decide +kernel
theorem part01_length : part01.length = 13 := by decide +kernel
end Snaky.Geometry14
