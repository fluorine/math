import Snaky.E1Checks12Part0
import Snaky.E1Checks12Part1
import Snaky.E1Checks12Part2
import Snaky.E1Checks12Part3
import Snaky.E1Checks12Part4
import Snaky.E1Checks12Part5
import Snaky.E1Checks12Part6
import Snaky.E1Checks12Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks12 : List Nat := [412, 413, 414, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444]
theorem masks12_checked : masks12.all checkMask = true := by
  simp only [masks12, List.all_cons, List.all_nil, mask412_checked, mask413_checked, mask414_checked, mask416_checked, mask417_checked, mask418_checked, mask419_checked, mask420_checked, mask421_checked, mask422_checked, mask423_checked, mask424_checked, mask425_checked, mask426_checked, mask427_checked, mask428_checked, mask429_checked, mask430_checked, mask431_checked, mask432_checked, mask433_checked, mask434_checked, mask435_checked, mask436_checked, mask437_checked, mask438_checked, mask439_checked, mask440_checked, mask441_checked, mask442_checked, mask443_checked, mask444_checked, Bool.and_self]

end Snaky.E1
