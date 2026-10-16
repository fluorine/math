import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice37_eq : slice orient3 7 = part37 := by decide +kernel
theorem part37_length : part37.length = 6 := by decide +kernel
end Snaky.Geometry10
