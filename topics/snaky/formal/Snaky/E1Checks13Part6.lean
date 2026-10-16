import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask471_checked : checkMask 471 = true := by decide +kernel
theorem mask472_checked : checkMask 472 = true := by decide +kernel
theorem mask473_checked : checkMask 473 = true := by decide +kernel
theorem mask474_checked : checkMask 474 = true := by decide +kernel

end Snaky.E1
