import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask309_checked : checkMask 309 = true := by decide +kernel
theorem mask310_checked : checkMask 310 = true := by decide +kernel
theorem mask311_checked : checkMask 311 = true := by decide +kernel
theorem mask312_checked : checkMask 312 = true := by decide +kernel

end Snaky.E1
