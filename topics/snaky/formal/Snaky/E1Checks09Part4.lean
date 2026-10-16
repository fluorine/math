import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask327_checked : checkMask 327 = true := by decide +kernel
theorem mask328_checked : checkMask 328 = true := by decide +kernel
theorem mask329_checked : checkMask 329 = true := by decide +kernel
theorem mask330_checked : checkMask 330 = true := by decide +kernel

end Snaky.E1
