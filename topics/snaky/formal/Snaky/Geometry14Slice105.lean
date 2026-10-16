import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice105_eq : slice orient7 7 = part105 := by decide +kernel
theorem part105_length : part105.length = 10 := by decide +kernel
end Snaky.Geometry14
