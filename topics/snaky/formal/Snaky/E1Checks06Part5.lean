import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask224_checked : checkMask 224 = true := by decide +kernel
theorem mask225_checked : checkMask 225 = true := by decide +kernel
theorem mask226_checked : checkMask 226 = true := by decide +kernel
theorem mask227_checked : checkMask 227 = true := by decide +kernel

end Snaky.E1
