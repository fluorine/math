import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask132_checked : checkMask 132 = true := by decide +kernel
theorem mask133_checked : checkMask 133 = true := by decide +kernel
theorem mask134_checked : checkMask 134 = true := by decide +kernel
theorem mask135_checked : checkMask 135 = true := by decide +kernel

end Snaky.E1
