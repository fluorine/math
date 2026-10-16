import Snaky.E1Checks09Part0
import Snaky.E1Checks09Part1
import Snaky.E1Checks09Part2
import Snaky.E1Checks09Part3
import Snaky.E1Checks09Part4
import Snaky.E1Checks09Part5
import Snaky.E1Checks09Part6
import Snaky.E1Checks09Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks09 : List Nat := [309, 310, 311, 312, 313, 314, 315, 316, 317, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342]
theorem masks09_checked : masks09.all checkMask = true := by
  simp only [masks09, List.all_cons, List.all_nil, mask309_checked, mask310_checked, mask311_checked, mask312_checked, mask313_checked, mask314_checked, mask315_checked, mask316_checked, mask317_checked, mask320_checked, mask321_checked, mask322_checked, mask323_checked, mask324_checked, mask325_checked, mask326_checked, mask327_checked, mask328_checked, mask329_checked, mask330_checked, mask331_checked, mask332_checked, mask333_checked, mask334_checked, mask335_checked, mask336_checked, mask337_checked, mask338_checked, mask339_checked, mask340_checked, mask341_checked, mask342_checked, Bool.and_self]

end Snaky.E1
