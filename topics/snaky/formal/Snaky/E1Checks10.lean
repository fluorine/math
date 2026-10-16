import Snaky.E1Checks10Part0
import Snaky.E1Checks10Part1
import Snaky.E1Checks10Part2
import Snaky.E1Checks10Part3
import Snaky.E1Checks10Part4
import Snaky.E1Checks10Part5
import Snaky.E1Checks10Part6
import Snaky.E1Checks10Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks10 : List Nat := [343, 344, 345, 346, 347, 348, 349, 350, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375]
theorem masks10_checked : masks10.all checkMask = true := by
  simp only [masks10, List.all_cons, List.all_nil, mask343_checked, mask344_checked, mask345_checked, mask346_checked, mask347_checked, mask348_checked, mask349_checked, mask350_checked, mask352_checked, mask353_checked, mask354_checked, mask355_checked, mask356_checked, mask357_checked, mask358_checked, mask359_checked, mask360_checked, mask361_checked, mask362_checked, mask363_checked, mask364_checked, mask365_checked, mask366_checked, mask367_checked, mask368_checked, mask369_checked, mask370_checked, mask371_checked, mask372_checked, mask373_checked, mask374_checked, mask375_checked, Bool.and_self]

end Snaky.E1
