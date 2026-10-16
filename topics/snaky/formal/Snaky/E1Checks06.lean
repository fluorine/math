import Snaky.E1Checks06Part0
import Snaky.E1Checks06Part1
import Snaky.E1Checks06Part2
import Snaky.E1Checks06Part3
import Snaky.E1Checks06Part4
import Snaky.E1Checks06Part5
import Snaky.E1Checks06Part6
import Snaky.E1Checks06Part7

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def masks06 : List Nat := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235]
theorem masks06_checked : masks06.all checkMask = true := by
  simp only [masks06, List.all_cons, List.all_nil, mask203_checked, mask204_checked, mask205_checked, mask206_checked, mask207_checked, mask208_checked, mask209_checked, mask210_checked, mask211_checked, mask212_checked, mask213_checked, mask214_checked, mask215_checked, mask216_checked, mask217_checked, mask218_checked, mask219_checked, mask220_checked, mask221_checked, mask222_checked, mask224_checked, mask225_checked, mask226_checked, mask227_checked, mask228_checked, mask229_checked, mask230_checked, mask231_checked, mask232_checked, mask233_checked, mask234_checked, mask235_checked, Bool.and_self]

end Snaky.E1
