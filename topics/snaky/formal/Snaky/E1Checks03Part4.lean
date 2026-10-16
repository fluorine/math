import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask116_checked : checkMask 116 = true := by decide +kernel
theorem mask117_checked : checkMask 117 = true := by decide +kernel
theorem mask118_checked : checkMask 118 = true := by decide +kernel
theorem mask119_checked : checkMask 119 = true := by decide +kernel

end Snaky.E1
