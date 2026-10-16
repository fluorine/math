import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask459_checked : checkMask 459 = true := by decide +kernel
theorem mask460_checked : checkMask 460 = true := by decide +kernel
theorem mask461_checked : checkMask 461 = true := by decide +kernel
theorem mask462_checked : checkMask 462 = true := by decide +kernel

end Snaky.E1
