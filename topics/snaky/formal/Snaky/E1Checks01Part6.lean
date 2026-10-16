import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask57_checked : checkMask 57 = true := by decide +kernel
theorem mask58_checked : checkMask 58 = true := by decide +kernel
theorem mask59_checked : checkMask 59 = true := by decide +kernel
theorem mask60_checked : checkMask 60 = true := by decide +kernel

end Snaky.E1
