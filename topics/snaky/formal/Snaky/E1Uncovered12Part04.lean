import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered12_part04 : sourcesPart04.filter (fun t => !covered pairs12 t) = [[22, 23, 33, 34, 35, 36], [24, 25, 31, 32, 33, 34], [24, 25, 35, 36, 37, 38]] := by decide +kernel

end Snaky.E1
