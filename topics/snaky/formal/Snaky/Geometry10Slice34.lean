import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice34_eq : slice orient3 4 = part34 := by decide +kernel
theorem part34_length : part34.length = 6 := by decide +kernel
end Snaky.Geometry10
