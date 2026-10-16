import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask484_checked : checkMask 484 = true := by decide +kernel
theorem mask485_checked : checkMask 485 = true := by decide +kernel
theorem mask486_checked : checkMask 486 = true := by decide +kernel
theorem mask487_checked : checkMask 487 = true := by decide +kernel

end Snaky.E1
