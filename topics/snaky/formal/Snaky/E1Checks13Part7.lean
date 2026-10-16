import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask475_checked : checkMask 475 = true := by decide +kernel
theorem mask476_checked : checkMask 476 = true := by decide +kernel
theorem mask477_checked : checkMask 477 = true := by decide +kernel
theorem mask478_checked : checkMask 478 = true := by decide +kernel

end Snaky.E1
