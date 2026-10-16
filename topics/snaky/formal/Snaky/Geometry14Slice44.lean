import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice44_eq : slice orient3 2 = part44 := by decide +kernel
theorem part44_length : part44.length = 10 := by decide +kernel
end Snaky.Geometry14
