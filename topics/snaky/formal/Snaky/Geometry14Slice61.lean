import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice61_eq : slice orient4 5 = part61 := by decide +kernel
theorem part61_length : part61.length = 13 := by decide +kernel
end Snaky.Geometry14
