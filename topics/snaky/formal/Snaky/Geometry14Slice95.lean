import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice95_eq : slice orient6 11 = part95 := by decide +kernel
theorem part95_length : part95.length = 0 := by decide +kernel
end Snaky.Geometry14
