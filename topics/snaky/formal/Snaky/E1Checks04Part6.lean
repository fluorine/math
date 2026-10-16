import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask161_checked : checkMask 161 = true := by decide +kernel
theorem mask162_checked : checkMask 162 = true := by decide +kernel
theorem mask163_checked : checkMask 163 = true := by decide +kernel
theorem mask164_checked : checkMask 164 = true := by decide +kernel

end Snaky.E1
