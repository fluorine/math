import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask211_checked : checkMask 211 = true := by decide +kernel
theorem mask212_checked : checkMask 212 = true := by decide +kernel
theorem mask213_checked : checkMask 213 = true := by decide +kernel
theorem mask214_checked : checkMask 214 = true := by decide +kernel

end Snaky.E1
