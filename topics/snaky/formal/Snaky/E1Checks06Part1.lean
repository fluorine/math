import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask207_checked : checkMask 207 = true := by decide +kernel
theorem mask208_checked : checkMask 208 = true := by decide +kernel
theorem mask209_checked : checkMask 209 = true := by decide +kernel
theorem mask210_checked : checkMask 210 = true := by decide +kernel

end Snaky.E1
