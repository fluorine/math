import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask12_checked : checkMask 12 = true := by decide +kernel
theorem mask13_checked : checkMask 13 = true := by decide +kernel
theorem mask14_checked : checkMask 14 = true := by decide +kernel
theorem mask15_checked : checkMask 15 = true := by decide +kernel

end Snaky.E1
