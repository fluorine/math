import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask256_checked : checkMask 256 = true := by decide +kernel
theorem mask257_checked : checkMask 257 = true := by decide +kernel
theorem mask258_checked : checkMask 258 = true := by decide +kernel
theorem mask259_checked : checkMask 259 = true := by decide +kernel

end Snaky.E1
