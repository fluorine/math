import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask24_checked : checkMask 24 = true := by decide +kernel
theorem mask25_checked : checkMask 25 = true := by decide +kernel
theorem mask26_checked : checkMask 26 = true := by decide +kernel
theorem mask27_checked : checkMask 27 = true := by decide +kernel

end Snaky.E1
