import Snaky.E1Checks08Part0
import Snaky.E1Checks08Part1
import Snaky.E1Checks08Part2
import Snaky.E1Checks08Part3
import Snaky.E1Checks08Part4
import Snaky.E1Checks08Part5
import Snaky.E1Checks08Part6
import Snaky.E1Checks08Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks08 : List Nat := [276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308]
theorem masks08_checked : masks08.all checkMask = true := by
  simp only [masks08, List.all_cons, List.all_nil, mask276_checked, mask277_checked, mask278_checked, mask279_checked, mask280_checked, mask281_checked, mask282_checked, mask283_checked, mask284_checked, mask285_checked, mask286_checked, mask288_checked, mask289_checked, mask290_checked, mask291_checked, mask292_checked, mask293_checked, mask294_checked, mask295_checked, mask296_checked, mask297_checked, mask298_checked, mask299_checked, mask300_checked, mask301_checked, mask302_checked, mask303_checked, mask304_checked, mask305_checked, mask306_checked, mask307_checked, mask308_checked, Bool.and_self]

end Snaky.E1
