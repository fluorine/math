import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice103_eq : slice orient7 5 = part103 := by decide +kernel
theorem part103_length : part103.length = 10 := by decide +kernel
end Snaky.Geometry14
