import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask317_checked : checkMask 317 = true := by decide +kernel
theorem mask320_checked : checkMask 320 = true := by decide +kernel
theorem mask321_checked : checkMask 321 = true := by decide +kernel
theorem mask322_checked : checkMask 322 = true := by decide +kernel

end Snaky.E1
