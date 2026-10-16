import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask276_checked : checkMask 276 = true := by decide +kernel
theorem mask277_checked : checkMask 277 = true := by decide +kernel
theorem mask278_checked : checkMask 278 = true := by decide +kernel
theorem mask279_checked : checkMask 279 = true := by decide +kernel

end Snaky.E1
