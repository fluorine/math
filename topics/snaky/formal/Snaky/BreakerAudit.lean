import Snaky.P52Audit
import Snaky.BreakerLRow
import Snaky.BreakerLCap
import Snaky.BreakerS11
import Snaky.BreakerS13
import Snaky.BreakerPostM31
import Snaky.BreakerP53Leaf
import Snaky.BreakerC30
import Snaky.BreakerN33
import Snaky.BreakerN32
import Snaky.BreakerAdmission35

/-! Actual ordinary-game conditional defenses. This audit does not claim a
result at any predecessor, an empty board, or all entries of an open parent. -/

#check Snaky.BreakerLRow.not_blackWins
#print axioms Snaky.BreakerLRow.not_blackWins
#check Snaky.BreakerLCap.not_blackWins
#print axioms Snaky.BreakerLCap.not_blackWins
#check Snaky.BreakerS11.not_blackWins
#print axioms Snaky.BreakerS11.not_blackWins
#check Snaky.BreakerS13.not_blackWins
#print axioms Snaky.BreakerS13.not_blackWins
#check Snaky.BreakerPostM31.not_blackWins
#print axioms Snaky.BreakerPostM31.not_blackWins
#check Snaky.BreakerP53Leaf.not_blackWins
#print axioms Snaky.BreakerP53Leaf.not_blackWins
#check Snaky.BreakerC30.not_blackWins
#print axioms Snaky.BreakerC30.not_blackWins
#check Snaky.BreakerN33.not_blackWins
#print axioms Snaky.BreakerN33.not_blackWins
#check Snaky.BreakerN32.not_blackWins
#print axioms Snaky.BreakerN32.not_blackWins
#check Snaky.BreakerAdmission35.not_blackWins
#print axioms Snaky.BreakerAdmission35.not_blackWins

#print axioms Snaky.Breaker.product_not_blackWins
#print axioms Snaky.Breaker.partial_matching_not_blackWins
