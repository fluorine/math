import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered01_part04 : sourcesPart04.filter (fun t => !covered pairs01 t) = [[21, 22, 32, 33, 34, 35], [23, 24, 30, 31, 32, 33], [23, 24, 34, 35, 36, 37]] := by decide +kernel

end Snaky.E1
