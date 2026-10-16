import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask272_checked : checkMask 272 = true := by decide +kernel
theorem mask273_checked : checkMask 273 = true := by decide +kernel
theorem mask274_checked : checkMask 274 = true := by decide +kernel
theorem mask275_checked : checkMask 275 = true := by decide +kernel

end Snaky.E1
