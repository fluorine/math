import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask264_checked : checkMask 264 = true := by decide +kernel
theorem mask265_checked : checkMask 265 = true := by decide +kernel
theorem mask266_checked : checkMask 266 = true := by decide +kernel
theorem mask267_checked : checkMask 267 = true := by decide +kernel

end Snaky.E1
