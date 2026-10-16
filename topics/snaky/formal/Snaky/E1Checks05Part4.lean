import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask185_checked : checkMask 185 = true := by decide +kernel
theorem mask186_checked : checkMask 186 = true := by decide +kernel
theorem mask187_checked : checkMask 187 = true := by decide +kernel
theorem mask188_checked : checkMask 188 = true := by decide +kernel

end Snaky.E1
