import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask339_checked : checkMask 339 = true := by decide +kernel
theorem mask340_checked : checkMask 340 = true := by decide +kernel
theorem mask341_checked : checkMask 341 = true := by decide +kernel
theorem mask342_checked : checkMask 342 = true := by decide +kernel

end Snaky.E1
