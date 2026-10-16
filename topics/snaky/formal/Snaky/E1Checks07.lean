import Snaky.E1Checks07Part0
import Snaky.E1Checks07Part1
import Snaky.E1Checks07Part2
import Snaky.E1Checks07Part3
import Snaky.E1Checks07Part4
import Snaky.E1Checks07Part5
import Snaky.E1Checks07Part6
import Snaky.E1Checks07Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks07 : List Nat := [236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275]
theorem masks07_checked : masks07.all checkMask = true := by
  simp only [masks07, List.all_cons, List.all_nil, mask236_checked, mask237_checked, mask238_checked, mask239_checked, mask240_checked, mask241_checked, mask242_checked, mask243_checked, mask244_checked, mask245_checked, mask246_checked, mask247_checked, mask256_checked, mask257_checked, mask258_checked, mask259_checked, mask260_checked, mask261_checked, mask262_checked, mask263_checked, mask264_checked, mask265_checked, mask266_checked, mask267_checked, mask268_checked, mask269_checked, mask270_checked, mask271_checked, mask272_checked, mask273_checked, mask274_checked, mask275_checked, Bool.and_self]

end Snaky.E1
