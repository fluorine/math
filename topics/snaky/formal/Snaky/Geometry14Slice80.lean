import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice80_eq : slice orient5 10 = part80 := by decide +kernel
theorem part80_length : part80.length = 10 := by decide +kernel
end Snaky.Geometry14
