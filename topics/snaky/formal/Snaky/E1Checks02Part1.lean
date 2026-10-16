import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask71_checked : checkMask 71 = true := by decide +kernel
theorem mask72_checked : checkMask 72 = true := by decide +kernel
theorem mask73_checked : checkMask 73 = true := by decide +kernel
theorem mask74_checked : checkMask 74 = true := by decide +kernel

end Snaky.E1
