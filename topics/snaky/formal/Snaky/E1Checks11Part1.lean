import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask384_checked : checkMask 384 = true := by decide +kernel
theorem mask385_checked : checkMask 385 = true := by decide +kernel
theorem mask386_checked : checkMask 386 = true := by decide +kernel
theorem mask387_checked : checkMask 387 = true := by decide +kernel

end Snaky.E1
