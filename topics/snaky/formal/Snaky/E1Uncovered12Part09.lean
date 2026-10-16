import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered12_part09 : sourcesPart09.filter (fun t => !covered pairs12 t) = [[71, 72, 82, 85]] := by decide +kernel

end Snaky.E1
