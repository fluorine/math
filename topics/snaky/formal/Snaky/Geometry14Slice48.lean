import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice48_eq : slice orient3 6 = part48 := by decide +kernel
theorem part48_length : part48.length = 10 := by decide +kernel
end Snaky.Geometry14
