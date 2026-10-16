import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice23_eq : slice orient1 9 = part23 := by decide +kernel
theorem part23_length : part23.length = 10 := by decide +kernel
end Snaky.Geometry14
