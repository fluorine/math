import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask404_checked : checkMask 404 = true := by decide +kernel
theorem mask405_checked : checkMask 405 = true := by decide +kernel
theorem mask406_checked : checkMask 406 = true := by decide +kernel
theorem mask407_checked : checkMask 407 = true := by decide +kernel

end Snaky.E1
