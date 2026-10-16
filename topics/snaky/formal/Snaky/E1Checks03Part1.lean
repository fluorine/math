import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask104_checked : checkMask 104 = true := by decide +kernel
theorem mask105_checked : checkMask 105 = true := by decide +kernel
theorem mask106_checked : checkMask 106 = true := by decide +kernel
theorem mask107_checked : checkMask 107 = true := by decide +kernel

end Snaky.E1
