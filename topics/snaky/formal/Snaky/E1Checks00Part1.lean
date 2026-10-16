import Snaky.E1Conditions

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mask4_checked : checkMask 4 = true := by decide +kernel
theorem mask5_checked : checkMask 5 = true := by decide +kernel
theorem mask6_checked : checkMask 6 = true := by decide +kernel
theorem mask7_checked : checkMask 7 = true := by decide +kernel

end Snaky.E1
