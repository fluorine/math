import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask268_checked : checkMask 268 = true := by decide +kernel
theorem mask269_checked : checkMask 269 = true := by decide +kernel
theorem mask270_checked : checkMask 270 = true := by decide +kernel
theorem mask271_checked : checkMask 271 = true := by decide +kernel

end Snaky.E1
