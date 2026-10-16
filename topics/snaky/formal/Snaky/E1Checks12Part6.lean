import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask437_checked : checkMask 437 = true := by decide +kernel
theorem mask438_checked : checkMask 438 = true := by decide +kernel
theorem mask439_checked : checkMask 439 = true := by decide +kernel
theorem mask440_checked : checkMask 440 = true := by decide +kernel

end Snaky.E1
