import Snaky.Geometry10Data

namespace Snaky.Geometry10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice63_eq : slice orient6 3 = part63 := by decide +kernel
theorem part63_length : part63.length = 9 := by decide +kernel
end Snaky.Geometry10
