import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered10_part07 : sourcesPart07.filter (fun t => !covered pairs10 t) = [[42, 52, 53, 63, 73], [43, 53, 63, 73, 74]] := by decide +kernel

end Snaky.E1
