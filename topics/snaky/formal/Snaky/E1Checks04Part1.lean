import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask140_checked : checkMask 140 = true := by decide +kernel
theorem mask141_checked : checkMask 141 = true := by decide +kernel
theorem mask142_checked : checkMask 142 = true := by decide +kernel
theorem mask143_checked : checkMask 143 = true := by decide +kernel

end Snaky.E1
