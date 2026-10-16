import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask451_checked : checkMask 451 = true := by decide +kernel
theorem mask452_checked : checkMask 452 = true := by decide +kernel
theorem mask453_checked : checkMask 453 = true := by decide +kernel
theorem mask454_checked : checkMask 454 = true := by decide +kernel

end Snaky.E1
