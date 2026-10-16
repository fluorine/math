import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask195_checked : checkMask 195 = true := by decide +kernel
theorem mask196_checked : checkMask 196 = true := by decide +kernel
theorem mask197_checked : checkMask 197 = true := by decide +kernel
theorem mask198_checked : checkMask 198 = true := by decide +kernel

end Snaky.E1
