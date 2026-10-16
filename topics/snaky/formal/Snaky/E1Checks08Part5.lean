import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask297_checked : checkMask 297 = true := by decide +kernel
theorem mask298_checked : checkMask 298 = true := by decide +kernel
theorem mask299_checked : checkMask 299 = true := by decide +kernel
theorem mask300_checked : checkMask 300 = true := by decide +kernel

end Snaky.E1
