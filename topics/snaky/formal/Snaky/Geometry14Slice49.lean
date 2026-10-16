import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice49_eq : slice orient3 7 = part49 := by decide +kernel
theorem part49_length : part49.length = 10 := by decide +kernel
end Snaky.Geometry14
