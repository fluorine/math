import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered12_part07 : sourcesPart07.filter (fun t => !covered pairs12 t) = [[42, 52, 53, 63, 73], [43, 53, 63, 72, 73, 82], [47, 57, 58, 68, 78, 88], [48, 58, 68, 77, 78, 87]] := by decide +kernel

end Snaky.E1
