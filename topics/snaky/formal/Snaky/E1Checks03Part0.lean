import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask100_checked : checkMask 100 = true := by decide +kernel
theorem mask101_checked : checkMask 101 = true := by decide +kernel
theorem mask102_checked : checkMask 102 = true := by decide +kernel
theorem mask103_checked : checkMask 103 = true := by decide +kernel

end Snaky.E1
