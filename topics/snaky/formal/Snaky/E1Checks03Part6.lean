import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask128_checked : checkMask 128 = true := by decide +kernel
theorem mask129_checked : checkMask 129 = true := by decide +kernel
theorem mask130_checked : checkMask 130 = true := by decide +kernel
theorem mask131_checked : checkMask 131 = true := by decide +kernel

end Snaky.E1
