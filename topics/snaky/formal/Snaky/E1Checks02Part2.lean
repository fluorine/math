import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask75_checked : checkMask 75 = true := by decide +kernel
theorem mask76_checked : checkMask 76 = true := by decide +kernel
theorem mask77_checked : checkMask 77 = true := by decide +kernel
theorem mask78_checked : checkMask 78 = true := by decide +kernel

end Snaky.E1
