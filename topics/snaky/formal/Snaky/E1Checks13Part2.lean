import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask455_checked : checkMask 455 = true := by decide +kernel
theorem mask456_checked : checkMask 456 = true := by decide +kernel
theorem mask457_checked : checkMask 457 = true := by decide +kernel
theorem mask458_checked : checkMask 458 = true := by decide +kernel

end Snaky.E1
