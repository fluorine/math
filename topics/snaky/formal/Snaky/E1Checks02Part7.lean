import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask96_checked : checkMask 96 = true := by decide +kernel
theorem mask97_checked : checkMask 97 = true := by decide +kernel
theorem mask98_checked : checkMask 98 = true := by decide +kernel
theorem mask99_checked : checkMask 99 = true := by decide +kernel

end Snaky.E1
