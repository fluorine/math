import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask305_checked : checkMask 305 = true := by decide +kernel
theorem mask306_checked : checkMask 306 = true := by decide +kernel
theorem mask307_checked : checkMask 307 = true := by decide +kernel
theorem mask308_checked : checkMask 308 = true := by decide +kernel

end Snaky.E1
