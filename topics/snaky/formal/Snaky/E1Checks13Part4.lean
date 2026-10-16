import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask463_checked : checkMask 463 = true := by decide +kernel
theorem mask464_checked : checkMask 464 = true := by decide +kernel
theorem mask465_checked : checkMask 465 = true := by decide +kernel
theorem mask466_checked : checkMask 466 = true := by decide +kernel

end Snaky.E1
