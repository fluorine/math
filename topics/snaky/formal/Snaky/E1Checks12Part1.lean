import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask417_checked : checkMask 417 = true := by decide +kernel
theorem mask418_checked : checkMask 418 = true := by decide +kernel
theorem mask419_checked : checkMask 419 = true := by decide +kernel
theorem mask420_checked : checkMask 420 = true := by decide +kernel

end Snaky.E1
