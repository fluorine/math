import Snaky.E1Checks11Part0
import Snaky.E1Checks11Part1
import Snaky.E1Checks11Part2
import Snaky.E1Checks11Part3
import Snaky.E1Checks11Part4
import Snaky.E1Checks11Part5
import Snaky.E1Checks11Part6
import Snaky.E1Checks11Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks11 : List Nat := [376, 377, 378, 379, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411]
theorem masks11_checked : masks11.all checkMask = true := by
  simp only [masks11, List.all_cons, List.all_nil, mask376_checked, mask377_checked, mask378_checked, mask379_checked, mask384_checked, mask385_checked, mask386_checked, mask387_checked, mask388_checked, mask389_checked, mask390_checked, mask391_checked, mask392_checked, mask393_checked, mask394_checked, mask395_checked, mask396_checked, mask397_checked, mask398_checked, mask399_checked, mask400_checked, mask401_checked, mask402_checked, mask403_checked, mask404_checked, mask405_checked, mask406_checked, mask407_checked, mask408_checked, mask409_checked, mask410_checked, mask411_checked, Bool.and_self]

end Snaky.E1
