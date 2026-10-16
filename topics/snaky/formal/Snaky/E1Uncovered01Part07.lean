import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered01_part07 : sourcesPart07.filter (fun t => !covered pairs01 t) = [[42, 52, 53, 63, 73], [43, 53, 63, 72, 73, 82]] := by decide +kernel

end Snaky.E1
