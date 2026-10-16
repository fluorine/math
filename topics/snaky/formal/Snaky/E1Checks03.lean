import Snaky.E1Checks03Part0
import Snaky.E1Checks03Part1
import Snaky.E1Checks03Part2
import Snaky.E1Checks03Part3
import Snaky.E1Checks03Part4
import Snaky.E1Checks03Part5
import Snaky.E1Checks03Part6
import Snaky.E1Checks03Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks03 : List Nat := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 128, 129, 130, 131, 132, 133, 134, 135]
theorem masks03_checked : masks03.all checkMask = true := by
  simp only [masks03, List.all_cons, List.all_nil, mask100_checked, mask101_checked, mask102_checked, mask103_checked, mask104_checked, mask105_checked, mask106_checked, mask107_checked, mask108_checked, mask109_checked, mask110_checked, mask111_checked, mask112_checked, mask113_checked, mask114_checked, mask115_checked, mask116_checked, mask117_checked, mask118_checked, mask119_checked, mask120_checked, mask121_checked, mask122_checked, mask123_checked, mask128_checked, mask129_checked, mask130_checked, mask131_checked, mask132_checked, mask133_checked, mask134_checked, mask135_checked, Bool.and_self]

end Snaky.E1
