import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask41_checked : checkMask 41 = true := by decide +kernel
theorem mask42_checked : checkMask 42 = true := by decide +kernel
theorem mask43_checked : checkMask 43 = true := by decide +kernel
theorem mask44_checked : checkMask 44 = true := by decide +kernel

end Snaky.E1
