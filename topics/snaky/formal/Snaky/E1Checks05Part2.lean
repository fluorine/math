import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask177_checked : checkMask 177 = true := by decide +kernel
theorem mask178_checked : checkMask 178 = true := by decide +kernel
theorem mask179_checked : checkMask 179 = true := by decide +kernel
theorem mask180_checked : checkMask 180 = true := by decide +kernel

end Snaky.E1
