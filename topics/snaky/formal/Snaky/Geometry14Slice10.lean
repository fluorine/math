import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice10_eq : slice orient0 10 = part10 := by decide +kernel
theorem part10_length : part10.length = 0 := by decide +kernel
end Snaky.Geometry14
