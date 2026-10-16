import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask429_checked : checkMask 429 = true := by decide +kernel
theorem mask430_checked : checkMask 430 = true := by decide +kernel
theorem mask431_checked : checkMask 431 = true := by decide +kernel
theorem mask432_checked : checkMask 432 = true := by decide +kernel

end Snaky.E1
