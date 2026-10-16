import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask120_checked : checkMask 120 = true := by decide +kernel
theorem mask121_checked : checkMask 121 = true := by decide +kernel
theorem mask122_checked : checkMask 122 = true := by decide +kernel
theorem mask123_checked : checkMask 123 = true := by decide +kernel

end Snaky.E1
