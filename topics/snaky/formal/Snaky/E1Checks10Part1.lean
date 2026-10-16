import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask347_checked : checkMask 347 = true := by decide +kernel
theorem mask348_checked : checkMask 348 = true := by decide +kernel
theorem mask349_checked : checkMask 349 = true := by decide +kernel
theorem mask350_checked : checkMask 350 = true := by decide +kernel

end Snaky.E1
