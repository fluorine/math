import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask412_checked : checkMask 412 = true := by decide +kernel
theorem mask413_checked : checkMask 413 = true := by decide +kernel
theorem mask414_checked : checkMask 414 = true := by decide +kernel
theorem mask416_checked : checkMask 416 = true := by decide +kernel

end Snaky.E1
