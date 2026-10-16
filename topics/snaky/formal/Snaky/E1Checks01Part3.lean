import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask45_checked : checkMask 45 = true := by decide +kernel
theorem mask46_checked : checkMask 46 = true := by decide +kernel
theorem mask47_checked : checkMask 47 = true := by decide +kernel
theorem mask48_checked : checkMask 48 = true := by decide +kernel

end Snaky.E1
