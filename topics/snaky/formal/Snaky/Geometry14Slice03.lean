import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice03_eq : slice orient0 3 = part03 := by decide +kernel
theorem part03_length : part03.length = 13 := by decide +kernel
end Snaky.Geometry14
