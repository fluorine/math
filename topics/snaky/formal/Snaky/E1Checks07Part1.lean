import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask240_checked : checkMask 240 = true := by decide +kernel
theorem mask241_checked : checkMask 241 = true := by decide +kernel
theorem mask242_checked : checkMask 242 = true := by decide +kernel
theorem mask243_checked : checkMask 243 = true := by decide +kernel

end Snaky.E1
