import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask492_checked : checkMask 492 = true := by decide +kernel
theorem mask493_checked : checkMask 493 = true := by decide +kernel
theorem mask494_checked : checkMask 494 = true := by decide +kernel

end Snaky.E1
