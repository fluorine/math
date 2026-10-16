import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice94_eq : slice orient6 10 = part94 := by decide +kernel
theorem part94_length : part94.length = 0 := by decide +kernel
end Snaky.Geometry14
