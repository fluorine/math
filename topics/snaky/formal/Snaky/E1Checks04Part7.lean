import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask165_checked : checkMask 165 = true := by decide +kernel
theorem mask166_checked : checkMask 166 = true := by decide +kernel
theorem mask167_checked : checkMask 167 = true := by decide +kernel
theorem mask168_checked : checkMask 168 = true := by decide +kernel

end Snaky.E1
