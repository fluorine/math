import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask169_checked : checkMask 169 = true := by decide +kernel
theorem mask170_checked : checkMask 170 = true := by decide +kernel
theorem mask171_checked : checkMask 171 = true := by decide +kernel
theorem mask172_checked : checkMask 172 = true := by decide +kernel

end Snaky.E1
