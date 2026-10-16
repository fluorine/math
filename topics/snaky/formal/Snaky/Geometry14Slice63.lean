import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice63_eq : slice orient4 7 = part63 := by decide +kernel
theorem part63_length : part63.length = 13 := by decide +kernel
end Snaky.Geometry14
