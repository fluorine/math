import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask376_checked : checkMask 376 = true := by decide +kernel
theorem mask377_checked : checkMask 377 = true := by decide +kernel
theorem mask378_checked : checkMask 378 = true := by decide +kernel
theorem mask379_checked : checkMask 379 = true := by decide +kernel

end Snaky.E1
