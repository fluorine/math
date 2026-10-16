import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered12_part01 : sourcesPart01.filter (fun t => !covered pairs12 t) = [] := by decide +kernel

end Snaky.E1
