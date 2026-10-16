import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask79_checked : checkMask 79 = true := by decide +kernel
theorem mask80_checked : checkMask 80 = true := by decide +kernel
theorem mask81_checked : checkMask 81 = true := by decide +kernel
theorem mask82_checked : checkMask 82 = true := by decide +kernel

end Snaky.E1
