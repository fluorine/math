import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask189_checked : checkMask 189 = true := by decide +kernel
theorem mask192_checked : checkMask 192 = true := by decide +kernel
theorem mask193_checked : checkMask 193 = true := by decide +kernel
theorem mask194_checked : checkMask 194 = true := by decide +kernel

end Snaky.E1
