import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask388_checked : checkMask 388 = true := by decide +kernel
theorem mask389_checked : checkMask 389 = true := by decide +kernel
theorem mask390_checked : checkMask 390 = true := by decide +kernel
theorem mask391_checked : checkMask 391 = true := by decide +kernel

end Snaky.E1
