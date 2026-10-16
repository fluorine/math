import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask136_checked : checkMask 136 = true := by decide +kernel
theorem mask137_checked : checkMask 137 = true := by decide +kernel
theorem mask138_checked : checkMask 138 = true := by decide +kernel
theorem mask139_checked : checkMask 139 = true := by decide +kernel

end Snaky.E1
