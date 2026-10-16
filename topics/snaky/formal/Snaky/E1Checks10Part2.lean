import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask352_checked : checkMask 352 = true := by decide +kernel
theorem mask353_checked : checkMask 353 = true := by decide +kernel
theorem mask354_checked : checkMask 354 = true := by decide +kernel
theorem mask355_checked : checkMask 355 = true := by decide +kernel

end Snaky.E1
