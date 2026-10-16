import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice72_eq : slice orient5 2 = part72 := by decide +kernel
theorem part72_length : part72.length = 10 := by decide +kernel
end Snaky.Geometry14
