import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask260_checked : checkMask 260 = true := by decide +kernel
theorem mask261_checked : checkMask 261 = true := by decide +kernel
theorem mask262_checked : checkMask 262 = true := by decide +kernel
theorem mask263_checked : checkMask 263 = true := by decide +kernel

end Snaky.E1
