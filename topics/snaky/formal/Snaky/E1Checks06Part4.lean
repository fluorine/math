import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask219_checked : checkMask 219 = true := by decide +kernel
theorem mask220_checked : checkMask 220 = true := by decide +kernel
theorem mask221_checked : checkMask 221 = true := by decide +kernel
theorem mask222_checked : checkMask 222 = true := by decide +kernel

end Snaky.E1
