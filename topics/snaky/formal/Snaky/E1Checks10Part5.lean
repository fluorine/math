import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask364_checked : checkMask 364 = true := by decide +kernel
theorem mask365_checked : checkMask 365 = true := by decide +kernel
theorem mask366_checked : checkMask 366 = true := by decide +kernel
theorem mask367_checked : checkMask 367 = true := by decide +kernel

end Snaky.E1
