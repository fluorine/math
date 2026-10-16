import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered11_part06 : sourcesPart06.filter (fun t => !covered pairs11 t) = [] := by decide +kernel

end Snaky.E1
