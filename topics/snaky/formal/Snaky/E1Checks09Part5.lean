import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask331_checked : checkMask 331 = true := by decide +kernel
theorem mask332_checked : checkMask 332 = true := by decide +kernel
theorem mask333_checked : checkMask 333 = true := by decide +kernel
theorem mask334_checked : checkMask 334 = true := by decide +kernel

end Snaky.E1
