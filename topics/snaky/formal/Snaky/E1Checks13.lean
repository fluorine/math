import Snaky.E1Checks13Part0
import Snaky.E1Checks13Part1
import Snaky.E1Checks13Part2
import Snaky.E1Checks13Part3
import Snaky.E1Checks13Part4
import Snaky.E1Checks13Part5
import Snaky.E1Checks13Part6
import Snaky.E1Checks13Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks13 : List Nat := [445, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478]
theorem masks13_checked : masks13.all checkMask = true := by
  simp only [masks13, List.all_cons, List.all_nil, mask445_checked, mask448_checked, mask449_checked, mask450_checked, mask451_checked, mask452_checked, mask453_checked, mask454_checked, mask455_checked, mask456_checked, mask457_checked, mask458_checked, mask459_checked, mask460_checked, mask461_checked, mask462_checked, mask463_checked, mask464_checked, mask465_checked, mask466_checked, mask467_checked, mask468_checked, mask469_checked, mask470_checked, mask471_checked, mask472_checked, mask473_checked, mask474_checked, mask475_checked, mask476_checked, mask477_checked, mask478_checked, Bool.and_self]

end Snaky.E1
