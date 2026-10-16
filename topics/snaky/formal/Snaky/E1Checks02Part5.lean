import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask87_checked : checkMask 87 = true := by decide +kernel
theorem mask88_checked : checkMask 88 = true := by decide +kernel
theorem mask89_checked : checkMask 89 = true := by decide +kernel
theorem mask90_checked : checkMask 90 = true := by decide +kernel

end Snaky.E1
