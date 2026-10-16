import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uncovered02_part03 : sourcesPart03.filter (fun t => !covered pairs02 t) = [] := by decide +kernel

end Snaky.E1
