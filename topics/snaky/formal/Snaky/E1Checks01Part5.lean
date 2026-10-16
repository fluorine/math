import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask53_checked : checkMask 53 = true := by decide +kernel
theorem mask54_checked : checkMask 54 = true := by decide +kernel
theorem mask55_checked : checkMask 55 = true := by decide +kernel
theorem mask56_checked : checkMask 56 = true := by decide +kernel

end Snaky.E1
