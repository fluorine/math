import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered11_part09 : sourcesPart09.filter (fun t => !covered pairs11 t) = [[65, 66, 67, 68, 74, 75], [71, 72, 82, 85]] := by decide +kernel

end Snaky.E1
