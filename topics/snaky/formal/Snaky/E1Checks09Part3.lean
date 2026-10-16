import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask323_checked : checkMask 323 = true := by decide +kernel
theorem mask324_checked : checkMask 324 = true := by decide +kernel
theorem mask325_checked : checkMask 325 = true := by decide +kernel
theorem mask326_checked : checkMask 326 = true := by decide +kernel

end Snaky.E1
