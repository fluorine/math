import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask49_checked : checkMask 49 = true := by decide +kernel
theorem mask50_checked : checkMask 50 = true := by decide +kernel
theorem mask51_checked : checkMask 51 = true := by decide +kernel
theorem mask52_checked : checkMask 52 = true := by decide +kernel

end Snaky.E1
