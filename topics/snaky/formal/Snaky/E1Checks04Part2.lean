import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask144_checked : checkMask 144 = true := by decide +kernel
theorem mask145_checked : checkMask 145 = true := by decide +kernel
theorem mask146_checked : checkMask 146 = true := by decide +kernel
theorem mask147_checked : checkMask 147 = true := by decide +kernel

end Snaky.E1
