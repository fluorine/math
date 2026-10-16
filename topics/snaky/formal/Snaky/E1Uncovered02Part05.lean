import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered02_part05 : sourcesPart05.filter (fun t => !covered pairs02 t) = [[25, 26, 32, 33, 34, 35], [27, 28, 34, 35, 36, 37]] := by decide +kernel

end Snaky.E1
