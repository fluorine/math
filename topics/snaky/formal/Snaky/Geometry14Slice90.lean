import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice90_eq : slice orient6 6 = part90 := by decide +kernel
theorem part90_length : part90.length = 13 := by decide +kernel
end Snaky.Geometry14
