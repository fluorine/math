import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask0_checked : checkMask 0 = true := by decide +kernel
theorem mask1_checked : checkMask 1 = true := by decide +kernel
theorem mask2_checked : checkMask 2 = true := by decide +kernel
theorem mask3_checked : checkMask 3 = true := by decide +kernel

end Snaky.E1
