import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice111_eq : slice orient7 13 = part111 := by decide +kernel
theorem part111_length : part111.length = 0 := by decide +kernel
end Snaky.Geometry14
