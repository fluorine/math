import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask425_checked : checkMask 425 = true := by decide +kernel
theorem mask426_checked : checkMask 426 = true := by decide +kernel
theorem mask427_checked : checkMask 427 = true := by decide +kernel
theorem mask428_checked : checkMask 428 = true := by decide +kernel

end Snaky.E1
