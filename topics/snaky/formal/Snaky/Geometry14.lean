import Snaky.Geometry14Group0
import Snaky.Geometry14Group1
import Snaky.Geometry14Group2
import Snaky.Geometry14Group3
import Snaky.Geometry14Group4
import Snaky.Geometry14Group5
import Snaky.Geometry14Group6
import Snaky.Geometry14Group7

namespace Snaky.Geometry14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem orientations_exact : orientations snaky = [orient0, orient1, orient2, orient3, orient4, orient5, orient6, orient7] := by decide +kernel
theorem placements_as_slices : placements 14 14 snaky =
    (orientations snaky).flatMap (fun o => (List.range 14).flatMap (slice o)) := rfl
theorem placements_eq_targets : placements 14 14 snaky = targets := by
  rw [placements_as_slices, orientations_exact, targets_eq_groups]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, group0_eq, group1_eq, group2_eq, group3_eq, group4_eq, group5_eq, group6_eq, group7_eq]

theorem target_count : (placements 14 14 snaky).length = 1040 := by
  rw [placements_eq_targets]
  simp only [targets, List.length_append, part00_length, part01_length, part02_length, part03_length, part04_length, part05_length, part06_length, part07_length, part08_length, part09_length, part10_length, part11_length, part12_length, part13_length, part14_length, part15_length, part16_length, part17_length, part18_length, part19_length, part20_length, part21_length, part22_length, part23_length, part24_length, part25_length, part26_length, part27_length, part28_length, part29_length, part30_length, part31_length, part32_length, part33_length, part34_length, part35_length, part36_length, part37_length, part38_length, part39_length, part40_length, part41_length, part42_length, part43_length, part44_length, part45_length, part46_length, part47_length, part48_length, part49_length, part50_length, part51_length, part52_length, part53_length, part54_length, part55_length, part56_length, part57_length, part58_length, part59_length, part60_length, part61_length, part62_length, part63_length, part64_length, part65_length, part66_length, part67_length, part68_length, part69_length, part70_length, part71_length, part72_length, part73_length, part74_length, part75_length, part76_length, part77_length, part78_length, part79_length, part80_length, part81_length, part82_length, part83_length, part84_length, part85_length, part86_length, part87_length, part88_length, part89_length, part90_length, part91_length, part92_length, part93_length, part94_length, part95_length, part96_length, part97_length, part98_length, part99_length, part100_length, part101_length, part102_length, part103_length, part104_length, part105_length, part106_length, part107_length, part108_length, part109_length, part110_length, part111_length]

end Snaky.Geometry14
