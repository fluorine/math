import Snaky.E1Checks02Part0
import Snaky.E1Checks02Part1
import Snaky.E1Checks02Part2
import Snaky.E1Checks02Part3
import Snaky.E1Checks02Part4
import Snaky.E1Checks02Part5
import Snaky.E1Checks02Part6
import Snaky.E1Checks02Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks02 : List Nat := [67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 96, 97, 98, 99]
theorem masks02_checked : masks02.all checkMask = true := by
  simp only [masks02, List.all_cons, List.all_nil, mask67_checked, mask68_checked, mask69_checked, mask70_checked, mask71_checked, mask72_checked, mask73_checked, mask74_checked, mask75_checked, mask76_checked, mask77_checked, mask78_checked, mask79_checked, mask80_checked, mask81_checked, mask82_checked, mask83_checked, mask84_checked, mask85_checked, mask86_checked, mask87_checked, mask88_checked, mask89_checked, mask90_checked, mask91_checked, mask92_checked, mask93_checked, mask94_checked, mask96_checked, mask97_checked, mask98_checked, mask99_checked, Bool.and_self]

end Snaky.E1
