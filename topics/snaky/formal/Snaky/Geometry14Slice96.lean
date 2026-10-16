import Snaky.Geometry14Data

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice96_eq : slice orient6 12 = part96 := by decide +kernel
theorem part96_length : part96.length = 0 := by decide +kernel
end Snaky.Geometry14
