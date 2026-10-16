import Snaky.E1Checks00Part0
import Snaky.E1Checks00Part1
import Snaky.E1Checks00Part2
import Snaky.E1Checks00Part3
import Snaky.E1Checks00Part4
import Snaky.E1Checks00Part5
import Snaky.E1Checks00Part6
import Snaky.E1Checks00Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks00 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32]
theorem masks00_checked : masks00.all checkMask = true := by
  simp only [masks00, List.all_cons, List.all_nil, mask0_checked, mask1_checked, mask2_checked, mask3_checked, mask4_checked, mask5_checked, mask6_checked, mask7_checked, mask8_checked, mask9_checked, mask10_checked, mask11_checked, mask12_checked, mask13_checked, mask14_checked, mask15_checked, mask16_checked, mask17_checked, mask18_checked, mask19_checked, mask20_checked, mask21_checked, mask22_checked, mask23_checked, mask24_checked, mask25_checked, mask26_checked, mask27_checked, mask28_checked, mask29_checked, mask30_checked, mask32_checked, Bool.and_self]

end Snaky.E1
