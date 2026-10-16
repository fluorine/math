import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask152_checked : checkMask 152 = true := by decide +kernel
theorem mask153_checked : checkMask 153 = true := by decide +kernel
theorem mask154_checked : checkMask 154 = true := by decide +kernel
theorem mask155_checked : checkMask 155 = true := by decide +kernel

end Snaky.E1
