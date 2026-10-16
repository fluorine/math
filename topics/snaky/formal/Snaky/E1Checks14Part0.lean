import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask480_checked : checkMask 480 = true := by decide +kernel
theorem mask481_checked : checkMask 481 = true := by decide +kernel
theorem mask482_checked : checkMask 482 = true := by decide +kernel
theorem mask483_checked : checkMask 483 = true := by decide +kernel

end Snaky.E1
