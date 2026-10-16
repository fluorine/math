import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice99_eq : slice orient7 1 = part99 := by decide +kernel
theorem part99_length : part99.length = 10 := by decide +kernel
end Snaky.Geometry14
