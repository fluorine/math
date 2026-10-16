import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask356_checked : checkMask 356 = true := by decide +kernel
theorem mask357_checked : checkMask 357 = true := by decide +kernel
theorem mask358_checked : checkMask 358 = true := by decide +kernel
theorem mask359_checked : checkMask 359 = true := by decide +kernel

end Snaky.E1
