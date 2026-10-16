import Snaky.E1Checks05Part0
import Snaky.E1Checks05Part1
import Snaky.E1Checks05Part2
import Snaky.E1Checks05Part3
import Snaky.E1Checks05Part4
import Snaky.E1Checks05Part5
import Snaky.E1Checks05Part6
import Snaky.E1Checks05Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks05 : List Nat := [169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
theorem masks05_checked : masks05.all checkMask = true := by
  simp only [masks05, List.all_cons, List.all_nil, mask169_checked, mask170_checked, mask171_checked, mask172_checked, mask173_checked, mask174_checked, mask175_checked, mask176_checked, mask177_checked, mask178_checked, mask179_checked, mask180_checked, mask181_checked, mask182_checked, mask183_checked, mask184_checked, mask185_checked, mask186_checked, mask187_checked, mask188_checked, mask189_checked, mask192_checked, mask193_checked, mask194_checked, mask195_checked, mask196_checked, mask197_checked, mask198_checked, mask199_checked, mask200_checked, mask201_checked, mask202_checked, Bool.and_self]

end Snaky.E1
