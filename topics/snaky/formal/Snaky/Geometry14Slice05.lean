import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice05_eq : slice orient0 5 = part05 := by decide +kernel
theorem part05_length : part05.length = 13 := by decide +kernel
end Snaky.Geometry14
