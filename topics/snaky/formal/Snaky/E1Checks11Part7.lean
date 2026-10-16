import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask408_checked : checkMask 408 = true := by decide +kernel
theorem mask409_checked : checkMask 409 = true := by decide +kernel
theorem mask410_checked : checkMask 410 = true := by decide +kernel
theorem mask411_checked : checkMask 411 = true := by decide +kernel

end Snaky.E1
