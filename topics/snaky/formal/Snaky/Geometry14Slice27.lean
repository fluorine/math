import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice27_eq : slice orient1 13 = part27 := by decide +kernel
theorem part27_length : part27.length = 0 := by decide +kernel
end Snaky.Geometry14
