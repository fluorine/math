import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask156_checked : checkMask 156 = true := by decide +kernel
theorem mask157_checked : checkMask 157 = true := by decide +kernel
theorem mask158_checked : checkMask 158 = true := by decide +kernel
theorem mask160_checked : checkMask 160 = true := by decide +kernel

end Snaky.E1
