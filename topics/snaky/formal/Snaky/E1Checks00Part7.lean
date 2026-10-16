import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask28_checked : checkMask 28 = true := by decide +kernel
theorem mask29_checked : checkMask 29 = true := by decide +kernel
theorem mask30_checked : checkMask 30 = true := by decide +kernel
theorem mask32_checked : checkMask 32 = true := by decide +kernel

end Snaky.E1
