import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask392_checked : checkMask 392 = true := by decide +kernel
theorem mask393_checked : checkMask 393 = true := by decide +kernel
theorem mask394_checked : checkMask 394 = true := by decide +kernel
theorem mask395_checked : checkMask 395 = true := by decide +kernel

end Snaky.E1
