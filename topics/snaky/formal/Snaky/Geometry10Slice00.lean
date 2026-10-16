import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice00_eq : slice orient0 0 = part00 := by decide +kernel
theorem part00_length : part00.length = 9 := by decide +kernel
end Snaky.Geometry10
