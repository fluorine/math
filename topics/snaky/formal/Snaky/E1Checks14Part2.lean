import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask488_checked : checkMask 488 = true := by decide +kernel
theorem mask489_checked : checkMask 489 = true := by decide +kernel
theorem mask490_checked : checkMask 490 = true := by decide +kernel
theorem mask491_checked : checkMask 491 = true := by decide +kernel

end Snaky.E1
