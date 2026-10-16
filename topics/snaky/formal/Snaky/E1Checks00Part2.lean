import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask8_checked : checkMask 8 = true := by decide +kernel
theorem mask9_checked : checkMask 9 = true := by decide +kernel
theorem mask10_checked : checkMask 10 = true := by decide +kernel
theorem mask11_checked : checkMask 11 = true := by decide +kernel

end Snaky.E1
