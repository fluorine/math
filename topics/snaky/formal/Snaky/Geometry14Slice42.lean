import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice42_eq : slice orient3 0 = part42 := by decide +kernel
theorem part42_length : part42.length = 10 := by decide +kernel
end Snaky.Geometry14
