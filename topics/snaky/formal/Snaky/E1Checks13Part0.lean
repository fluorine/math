import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask445_checked : checkMask 445 = true := by decide +kernel
theorem mask448_checked : checkMask 448 = true := by decide +kernel
theorem mask449_checked : checkMask 449 = true := by decide +kernel
theorem mask450_checked : checkMask 450 = true := by decide +kernel

end Snaky.E1
