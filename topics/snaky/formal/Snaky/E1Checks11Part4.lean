import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask396_checked : checkMask 396 = true := by decide +kernel
theorem mask397_checked : checkMask 397 = true := by decide +kernel
theorem mask398_checked : checkMask 398 = true := by decide +kernel
theorem mask399_checked : checkMask 399 = true := by decide +kernel

end Snaky.E1
