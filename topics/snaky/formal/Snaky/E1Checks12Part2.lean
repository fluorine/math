import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask421_checked : checkMask 421 = true := by decide +kernel
theorem mask422_checked : checkMask 422 = true := by decide +kernel
theorem mask423_checked : checkMask 423 = true := by decide +kernel
theorem mask424_checked : checkMask 424 = true := by decide +kernel

end Snaky.E1
