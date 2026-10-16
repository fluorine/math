import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask372_checked : checkMask 372 = true := by decide +kernel
theorem mask373_checked : checkMask 373 = true := by decide +kernel
theorem mask374_checked : checkMask 374 = true := by decide +kernel
theorem mask375_checked : checkMask 375 = true := by decide +kernel

end Snaky.E1
