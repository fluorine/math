import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice12_eq : slice orient0 12 = part12 := by decide +kernel
theorem part12_length : part12.length = 0 := by decide +kernel
end Snaky.Geometry14
