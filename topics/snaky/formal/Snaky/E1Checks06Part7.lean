import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask232_checked : checkMask 232 = true := by decide +kernel
theorem mask233_checked : checkMask 233 = true := by decide +kernel
theorem mask234_checked : checkMask 234 = true := by decide +kernel
theorem mask235_checked : checkMask 235 = true := by decide +kernel

end Snaky.E1
