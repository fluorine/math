import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask108_checked : checkMask 108 = true := by decide +kernel
theorem mask109_checked : checkMask 109 = true := by decide +kernel
theorem mask110_checked : checkMask 110 = true := by decide +kernel
theorem mask111_checked : checkMask 111 = true := by decide +kernel

end Snaky.E1
