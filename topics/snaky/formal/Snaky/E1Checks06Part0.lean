import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask203_checked : checkMask 203 = true := by decide +kernel
theorem mask204_checked : checkMask 204 = true := by decide +kernel
theorem mask205_checked : checkMask 205 = true := by decide +kernel
theorem mask206_checked : checkMask 206 = true := by decide +kernel

end Snaky.E1
