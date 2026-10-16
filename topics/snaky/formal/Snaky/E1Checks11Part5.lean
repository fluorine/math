import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask400_checked : checkMask 400 = true := by decide +kernel
theorem mask401_checked : checkMask 401 = true := by decide +kernel
theorem mask402_checked : checkMask 402 = true := by decide +kernel
theorem mask403_checked : checkMask 403 = true := by decide +kernel

end Snaky.E1
