import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask289_checked : checkMask 289 = true := by decide +kernel
theorem mask290_checked : checkMask 290 = true := by decide +kernel
theorem mask291_checked : checkMask 291 = true := by decide +kernel
theorem mask292_checked : checkMask 292 = true := by decide +kernel

end Snaky.E1
