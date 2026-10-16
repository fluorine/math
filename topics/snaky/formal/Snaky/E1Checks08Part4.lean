import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask293_checked : checkMask 293 = true := by decide +kernel
theorem mask294_checked : checkMask 294 = true := by decide +kernel
theorem mask295_checked : checkMask 295 = true := by decide +kernel
theorem mask296_checked : checkMask 296 = true := by decide +kernel

end Snaky.E1
