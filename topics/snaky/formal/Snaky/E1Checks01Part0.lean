import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask33_checked : checkMask 33 = true := by decide +kernel
theorem mask34_checked : checkMask 34 = true := by decide +kernel
theorem mask35_checked : checkMask 35 = true := by decide +kernel
theorem mask36_checked : checkMask 36 = true := by decide +kernel

end Snaky.E1
