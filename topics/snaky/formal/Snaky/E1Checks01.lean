import Snaky.E1Checks01Part0
import Snaky.E1Checks01Part1
import Snaky.E1Checks01Part2
import Snaky.E1Checks01Part3
import Snaky.E1Checks01Part4
import Snaky.E1Checks01Part5
import Snaky.E1Checks01Part6
import Snaky.E1Checks01Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks01 : List Nat := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 64, 65, 66]
theorem masks01_checked : masks01.all checkMask = true := by
  simp only [masks01, List.all_cons, List.all_nil, mask33_checked, mask34_checked, mask35_checked, mask36_checked, mask37_checked, mask38_checked, mask39_checked, mask40_checked, mask41_checked, mask42_checked, mask43_checked, mask44_checked, mask45_checked, mask46_checked, mask47_checked, mask48_checked, mask49_checked, mask50_checked, mask51_checked, mask52_checked, mask53_checked, mask54_checked, mask55_checked, mask56_checked, mask57_checked, mask58_checked, mask59_checked, mask60_checked, mask61_checked, mask64_checked, mask65_checked, mask66_checked, Bool.and_self]

end Snaky.E1
