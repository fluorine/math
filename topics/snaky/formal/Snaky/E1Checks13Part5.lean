import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask467_checked : checkMask 467 = true := by decide +kernel
theorem mask468_checked : checkMask 468 = true := by decide +kernel
theorem mask469_checked : checkMask 469 = true := by decide +kernel
theorem mask470_checked : checkMask 470 = true := by decide +kernel

end Snaky.E1
