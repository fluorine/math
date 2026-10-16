import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice31_eq : slice orient3 1 = part31 := by decide +kernel
theorem part31_length : part31.length = 6 := by decide +kernel
end Snaky.Geometry10
