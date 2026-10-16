import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask236_checked : checkMask 236 = true := by decide +kernel
theorem mask237_checked : checkMask 237 = true := by decide +kernel
theorem mask238_checked : checkMask 238 = true := by decide +kernel
theorem mask239_checked : checkMask 239 = true := by decide +kernel

end Snaky.E1
