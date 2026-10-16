import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice72_eq : slice orient7 2 = part72 := by decide +kernel
theorem part72_length : part72.length = 6 := by decide +kernel
end Snaky.Geometry10
