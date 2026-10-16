import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask148_checked : checkMask 148 = true := by decide +kernel
theorem mask149_checked : checkMask 149 = true := by decide +kernel
theorem mask150_checked : checkMask 150 = true := by decide +kernel
theorem mask151_checked : checkMask 151 = true := by decide +kernel

end Snaky.E1
