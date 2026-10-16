import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask280_checked : checkMask 280 = true := by decide +kernel
theorem mask281_checked : checkMask 281 = true := by decide +kernel
theorem mask282_checked : checkMask 282 = true := by decide +kernel
theorem mask283_checked : checkMask 283 = true := by decide +kernel

end Snaky.E1
