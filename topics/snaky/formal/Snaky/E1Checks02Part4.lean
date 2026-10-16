import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask83_checked : checkMask 83 = true := by decide +kernel
theorem mask84_checked : checkMask 84 = true := by decide +kernel
theorem mask85_checked : checkMask 85 = true := by decide +kernel
theorem mask86_checked : checkMask 86 = true := by decide +kernel

end Snaky.E1
