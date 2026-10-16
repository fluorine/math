import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask199_checked : checkMask 199 = true := by decide +kernel
theorem mask200_checked : checkMask 200 = true := by decide +kernel
theorem mask201_checked : checkMask 201 = true := by decide +kernel
theorem mask202_checked : checkMask 202 = true := by decide +kernel

end Snaky.E1
