import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask368_checked : checkMask 368 = true := by decide +kernel
theorem mask369_checked : checkMask 369 = true := by decide +kernel
theorem mask370_checked : checkMask 370 = true := by decide +kernel
theorem mask371_checked : checkMask 371 = true := by decide +kernel

end Snaky.E1
