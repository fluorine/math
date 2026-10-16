import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered01_part06 : sourcesPart06.filter (fun t => !covered pairs01 t) = [] := by decide +kernel

end Snaky.E1
