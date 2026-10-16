import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask313_checked : checkMask 313 = true := by decide +kernel
theorem mask314_checked : checkMask 314 = true := by decide +kernel
theorem mask315_checked : checkMask 315 = true := by decide +kernel
theorem mask316_checked : checkMask 316 = true := by decide +kernel

end Snaky.E1
