import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered10_part00 : sourcesPart00.filter (fun t => !covered pairs10 t) = [] := by decide +kernel

end Snaky.E1
