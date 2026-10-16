import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask284_checked : checkMask 284 = true := by decide +kernel
theorem mask285_checked : checkMask 285 = true := by decide +kernel
theorem mask286_checked : checkMask 286 = true := by decide +kernel
theorem mask288_checked : checkMask 288 = true := by decide +kernel

end Snaky.E1
