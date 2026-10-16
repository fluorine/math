import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice58_eq : slice orient5 8 = part58 := by decide +kernel
theorem part58_length : part58.length = 6 := by decide +kernel
end Snaky.Geometry10
