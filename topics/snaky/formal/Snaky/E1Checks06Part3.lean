import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask215_checked : checkMask 215 = true := by decide +kernel
theorem mask216_checked : checkMask 216 = true := by decide +kernel
theorem mask217_checked : checkMask 217 = true := by decide +kernel
theorem mask218_checked : checkMask 218 = true := by decide +kernel

end Snaky.E1
