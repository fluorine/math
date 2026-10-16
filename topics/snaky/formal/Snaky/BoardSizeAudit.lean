import Snaky.BreakerAudit
import Snaky.P52Audit
import Snaky.E1Audit
import Snaky.MakerCloseoutAudit
import Snaky.C30Audit
import Snaky.MakerOpeningAudit
import Snaky.RGapMatchingObstruction

/-! Closeout audit of conditional board-size results. No empty 14×14 Maker
result or empty 10×10 Breaker result is asserted. Opening bounds count
further Maker claims from the explicitly colored position. -/

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
#check Snaky.P52.not_blackWins
#print axioms Snaky.P52.not_blackWins
#check Snaky.P52.missing_pair_rejected
#check Snaky.P52.self_reply_rejected
#check Snaky.P52Continued.Endpoint52.not_blackWins
#print axioms Snaky.P52Continued.Endpoint52.not_blackWins
#check Snaky.P52Continued.Endpoint53.not_blackWins
#print axioms Snaky.P52Continued.Endpoint53.not_blackWins
#check Snaky.E1.e1_source_replacement
#check Snaky.E1.e1_physical_incidence_replacement
#check Snaky.E1.config_matching
#check Snaky.E1.source_dimensions
#print axioms Snaky.E1.e1_source_replacement
#print axioms Snaky.E1.e1_physical_incidence_replacement
#print axioms Snaky.E1.config_matching
#print axioms Snaky.E1.source_dimensions
#check Snaky.MakerCloseout.continuation_wins_in_eight
#check Snaky.MakerCloseout.n30_after_q_wins
#check Snaky.MakerCloseout.n31_after_q_wins
#check Snaky.MakerCloseout.initial_reply_counts
#check Snaky.MakerCloseout.initial_reply_partition
#check Snaky.MakerCloseout.n30_full_state
#check Snaky.MakerCloseout.n31_full_state
#print axioms Snaky.GenMakerCloseout.tree_ok
#print axioms Snaky.MakerCloseout.continuation_wins_in_eight
#print axioms Snaky.MakerCloseout.n30_after_q_wins
#print axioms Snaky.MakerCloseout.n31_after_q_wins
#print axioms Snaky.MakerCloseout.initial_reply_counts
#print axioms Snaky.MakerCloseout.initial_reply_partition
#print axioms Snaky.MakerCloseout.n30_full_state
#print axioms Snaky.MakerCloseout.n31_full_state
#check Snaky.C30Selected.selected_guards_win_in_ten
#check Snaky.C30Selected.selected_contract
#print axioms Snaky.SelectedAttack.sound
#print axioms Snaky.C30Selected.tree_ok
#print axioms Snaky.C30Selected.selected_guards_win_in_ten
#print axioms Snaky.C30Selected.selected_contract
#print axioms Snaky.SelectedAttack.Controls.domino_wins
#check Snaky.MakerOpening.opening_66_wins_in_nineteen
#check Snaky.MakerOpening.opening_710_wins_in_fifteen
#print axioms Snaky.MakerOpeningCheck.hint_of_parts
#print axioms Snaky.MakerOpeningCheck.hint_avoid
#print axioms Snaky.MakerOpeningCheck.reply_of_hint
#print axioms Snaky.GenMakerOpening.tree_ok
#print axioms Snaky.MakerOpening.opening66_placed
#print axioms Snaky.MakerOpening.opening710_placed
#print axioms Snaky.MakerOpening.opening_66_wins_in_nineteen
#print axioms Snaky.MakerOpening.opening_710_wins_in_fifteen
#check Snaky.RGapMatchingObstruction.no_static_matching
#print axioms Snaky.RGapMatchingObstruction.no_static_matching
