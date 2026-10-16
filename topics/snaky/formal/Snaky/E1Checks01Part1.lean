import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask37_checked : checkMask 37 = true := by decide +kernel
theorem mask38_checked : checkMask 38 = true := by decide +kernel
theorem mask39_checked : checkMask 39 = true := by decide +kernel
theorem mask40_checked : checkMask 40 = true := by decide +kernel

end Snaky.E1
