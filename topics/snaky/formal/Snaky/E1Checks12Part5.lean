import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask433_checked : checkMask 433 = true := by decide +kernel
theorem mask434_checked : checkMask 434 = true := by decide +kernel
theorem mask435_checked : checkMask 435 = true := by decide +kernel
theorem mask436_checked : checkMask 436 = true := by decide +kernel

end Snaky.E1
