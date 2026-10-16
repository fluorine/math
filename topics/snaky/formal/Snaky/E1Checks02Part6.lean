import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask91_checked : checkMask 91 = true := by decide +kernel
theorem mask92_checked : checkMask 92 = true := by decide +kernel
theorem mask93_checked : checkMask 93 = true := by decide +kernel
theorem mask94_checked : checkMask 94 = true := by decide +kernel

end Snaky.E1
