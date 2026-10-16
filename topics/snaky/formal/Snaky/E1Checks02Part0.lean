import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask67_checked : checkMask 67 = true := by decide +kernel
theorem mask68_checked : checkMask 68 = true := by decide +kernel
theorem mask69_checked : checkMask 69 = true := by decide +kernel
theorem mask70_checked : checkMask 70 = true := by decide +kernel

end Snaky.E1
