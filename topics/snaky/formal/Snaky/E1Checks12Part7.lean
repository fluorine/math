import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask441_checked : checkMask 441 = true := by decide +kernel
theorem mask442_checked : checkMask 442 = true := by decide +kernel
theorem mask443_checked : checkMask 443 = true := by decide +kernel
theorem mask444_checked : checkMask 444 = true := by decide +kernel

end Snaky.E1
