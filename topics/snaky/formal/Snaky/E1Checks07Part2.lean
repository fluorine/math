import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask244_checked : checkMask 244 = true := by decide +kernel
theorem mask245_checked : checkMask 245 = true := by decide +kernel
theorem mask246_checked : checkMask 246 = true := by decide +kernel
theorem mask247_checked : checkMask 247 = true := by decide +kernel

end Snaky.E1
