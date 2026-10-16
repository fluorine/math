import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask343_checked : checkMask 343 = true := by decide +kernel
theorem mask344_checked : checkMask 344 = true := by decide +kernel
theorem mask345_checked : checkMask 345 = true := by decide +kernel
theorem mask346_checked : checkMask 346 = true := by decide +kernel

end Snaky.E1
