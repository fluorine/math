import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice20_eq : slice orient2 0 = part20 := by decide +kernel
theorem part20_length : part20.length = 9 := by decide +kernel
end Snaky.Geometry10
