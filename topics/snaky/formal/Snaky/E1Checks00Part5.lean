import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask20_checked : checkMask 20 = true := by decide +kernel
theorem mask21_checked : checkMask 21 = true := by decide +kernel
theorem mask22_checked : checkMask 22 = true := by decide +kernel
theorem mask23_checked : checkMask 23 = true := by decide +kernel

end Snaky.E1
