import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered11_part05 : sourcesPart05.filter (fun t => !covered pairs11 t) = [[26, 27, 33, 34, 35, 36]] := by decide +kernel

end Snaky.E1
