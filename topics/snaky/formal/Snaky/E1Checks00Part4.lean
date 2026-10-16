import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask16_checked : checkMask 16 = true := by decide +kernel
theorem mask17_checked : checkMask 17 = true := by decide +kernel
theorem mask18_checked : checkMask 18 = true := by decide +kernel
theorem mask19_checked : checkMask 19 = true := by decide +kernel

end Snaky.E1
