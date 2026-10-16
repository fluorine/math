import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask112_checked : checkMask 112 = true := by decide +kernel
theorem mask113_checked : checkMask 113 = true := by decide +kernel
theorem mask114_checked : checkMask 114 = true := by decide +kernel
theorem mask115_checked : checkMask 115 = true := by decide +kernel

end Snaky.E1
