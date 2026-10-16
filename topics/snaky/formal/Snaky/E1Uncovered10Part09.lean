import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered10_part09 : sourcesPart09.filter (fun t => !covered pairs10 t) = [[73, 74, 80, 81, 82], [73, 74, 85, 86, 87]] := by decide +kernel

end Snaky.E1
