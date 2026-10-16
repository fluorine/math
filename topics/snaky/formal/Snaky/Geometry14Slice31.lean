import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice31_eq : slice orient2 3 = part31 := by decide +kernel
theorem part31_length : part31.length = 13 := by decide +kernel
end Snaky.Geometry14
