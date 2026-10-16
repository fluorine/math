import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask181_checked : checkMask 181 = true := by decide +kernel
theorem mask182_checked : checkMask 182 = true := by decide +kernel
theorem mask183_checked : checkMask 183 = true := by decide +kernel
theorem mask184_checked : checkMask 184 = true := by decide +kernel

end Snaky.E1
