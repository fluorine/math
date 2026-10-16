import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask228_checked : checkMask 228 = true := by decide +kernel
theorem mask229_checked : checkMask 229 = true := by decide +kernel
theorem mask230_checked : checkMask 230 = true := by decide +kernel
theorem mask231_checked : checkMask 231 = true := by decide +kernel

end Snaky.E1
