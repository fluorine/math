import Snaky.E1Checks14Part0
import Snaky.E1Checks14Part1
import Snaky.E1Checks14Part2
import Snaky.E1Checks14Part3

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks14 : List Nat := [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494]
theorem masks14_checked : masks14.all checkMask = true := by
  simp only [masks14, List.all_cons, List.all_nil, mask480_checked, mask481_checked, mask482_checked, mask483_checked, mask484_checked, mask485_checked, mask486_checked, mask487_checked, mask488_checked, mask489_checked, mask490_checked, mask491_checked, mask492_checked, mask493_checked, mask494_checked, Bool.and_self]

end Snaky.E1
