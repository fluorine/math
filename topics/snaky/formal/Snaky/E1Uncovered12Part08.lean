import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered12_part08 : sourcesPart08.filter (fun t => !covered pairs12 t) = [[57, 58, 64, 65, 66, 67], [64, 65, 66, 67, 77, 78]] := by decide +kernel

end Snaky.E1
