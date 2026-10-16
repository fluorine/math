import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask173_checked : checkMask 173 = true := by decide +kernel
theorem mask174_checked : checkMask 174 = true := by decide +kernel
theorem mask175_checked : checkMask 175 = true := by decide +kernel
theorem mask176_checked : checkMask 176 = true := by decide +kernel

end Snaky.E1
