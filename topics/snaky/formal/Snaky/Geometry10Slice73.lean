import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice73_eq : slice orient7 3 = part73 := by decide +kernel
theorem part73_length : part73.length = 6 := by decide +kernel
end Snaky.Geometry10
