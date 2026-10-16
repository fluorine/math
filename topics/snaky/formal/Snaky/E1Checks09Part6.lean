import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask335_checked : checkMask 335 = true := by decide +kernel
theorem mask336_checked : checkMask 336 = true := by decide +kernel
theorem mask337_checked : checkMask 337 = true := by decide +kernel
theorem mask338_checked : checkMask 338 = true := by decide +kernel

end Snaky.E1
