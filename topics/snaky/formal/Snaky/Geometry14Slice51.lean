import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice51_eq : slice orient3 9 = part51 := by decide +kernel
theorem part51_length : part51.length = 10 := by decide +kernel
end Snaky.Geometry14
