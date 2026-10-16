import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask301_checked : checkMask 301 = true := by decide +kernel
theorem mask302_checked : checkMask 302 = true := by decide +kernel
theorem mask303_checked : checkMask 303 = true := by decide +kernel
theorem mask304_checked : checkMask 304 = true := by decide +kernel

end Snaky.E1
