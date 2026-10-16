import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered00_part08 : sourcesPart08.filter (fun t => !covered pairs00 t) = [[60, 61, 62, 63, 73, 74], [64, 65, 66, 67, 73, 74]] := by decide +kernel

end Snaky.E1
