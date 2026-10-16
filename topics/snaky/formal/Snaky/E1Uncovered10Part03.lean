import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered10_part03 : sourcesPart03.filter (fun t => !covered pairs10 t) = [[20, 21, 31, 32, 33, 34]] := by decide +kernel

end Snaky.E1
