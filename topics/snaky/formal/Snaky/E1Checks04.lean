import Snaky.E1Checks04Part0
import Snaky.E1Checks04Part1
import Snaky.E1Checks04Part2
import Snaky.E1Checks04Part3
import Snaky.E1Checks04Part4
import Snaky.E1Checks04Part5
import Snaky.E1Checks04Part6
import Snaky.E1Checks04Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks04 : List Nat := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168]
theorem masks04_checked : masks04.all checkMask = true := by
  simp only [masks04, List.all_cons, List.all_nil, mask136_checked, mask137_checked, mask138_checked, mask139_checked, mask140_checked, mask141_checked, mask142_checked, mask143_checked, mask144_checked, mask145_checked, mask146_checked, mask147_checked, mask148_checked, mask149_checked, mask150_checked, mask151_checked, mask152_checked, mask153_checked, mask154_checked, mask155_checked, mask156_checked, mask157_checked, mask158_checked, mask160_checked, mask161_checked, mask162_checked, mask163_checked, mask164_checked, mask165_checked, mask166_checked, mask167_checked, mask168_checked, Bool.and_self]

end Snaky.E1
