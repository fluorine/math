import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask360_checked : checkMask 360 = true := by decide +kernel
theorem mask361_checked : checkMask 361 = true := by decide +kernel
theorem mask362_checked : checkMask 362 = true := by decide +kernel
theorem mask363_checked : checkMask 363 = true := by decide +kernel

end Snaky.E1
