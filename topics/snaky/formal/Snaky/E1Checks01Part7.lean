import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask61_checked : checkMask 61 = true := by decide +kernel
theorem mask64_checked : checkMask 64 = true := by decide +kernel
theorem mask65_checked : checkMask 65 = true := by decide +kernel
theorem mask66_checked : checkMask 66 = true := by decide +kernel

end Snaky.E1
