import Snaky.Geometry10
import Snaky.E1GeometryPart00
import Snaky.E1GeometryPart01
import Snaky.E1GeometryPart02
import Snaky.E1GeometryPart03
import Snaky.E1GeometryPart04
import Snaky.E1GeometryPart05
import Snaky.E1GeometryPart06
import Snaky.E1GeometryPart07
import Snaky.E1GeometryPart08
import Snaky.E1GeometryPart09
import Snaky.E1GeometryPart10
import Snaky.E1GeometryPart11
import Snaky.E1GeometryPart12
import Snaky.E1GeometryPart13
import Snaky.E1GeometryPart14
import Snaky.E1GeometryPart15
import Snaky.E1GeometryPart16
import Snaky.E1GeometryPart17
import Snaky.E1GeometryPart18
import Snaky.E1GeometryPart19
import Snaky.E1GeometryPart20
import Snaky.E1GeometryPart21
import Snaky.E1GeometryPart22
import Snaky.E1GeometryPart23
import Snaky.E1GeometryPart24
import Snaky.E1GeometryPart25
import Snaky.E1GeometryPart26
import Snaky.E1GeometryPart27
import Snaky.E1GeometryPart28
import Snaky.E1GeometryPart29
import Snaky.E1GeometryPart30
import Snaky.E1GeometryPart31
import Snaky.E1GeometryPart32
import Snaky.E1GeometryPart33
import Snaky.E1GeometryPart34
import Snaky.E1GeometryPart35
import Snaky.E1GeometryPart36
import Snaky.E1GeometryPart37
import Snaky.E1GeometryPart38
import Snaky.E1GeometryPart39
import Snaky.E1GeometryPart40
import Snaky.E1GeometryPart41
import Snaky.E1GeometryPart42
import Snaky.E1GeometryPart43
import Snaky.E1GeometryPart44
import Snaky.E1GeometryPart45
import Snaky.E1GeometryPart46
import Snaky.E1GeometryPart47
import Snaky.E1GeometryPart48
import Snaky.E1GeometryPart49
import Snaky.E1GeometryPart50
import Snaky.E1GeometryPart51
import Snaky.E1GeometryPart52
import Snaky.E1GeometryPart53
import Snaky.E1GeometryPart54
import Snaky.E1GeometryPart55
import Snaky.E1GeometryPart56
import Snaky.E1GeometryPart57
import Snaky.E1GeometryPart58
import Snaky.E1GeometryPart59
import Snaky.E1GeometryPart60
import Snaky.E1GeometryPart61
import Snaky.E1GeometryPart62
import Snaky.E1GeometryPart63
import Snaky.E1GeometryPart64
import Snaky.E1GeometryPart65
import Snaky.E1GeometryPart66
import Snaky.E1GeometryPart67
import Snaky.E1GeometryPart68
import Snaky.E1GeometryPart69
import Snaky.E1GeometryPart70
import Snaky.E1GeometryPart71
import Snaky.E1GeometryPart72
import Snaky.E1GeometryPart73
import Snaky.E1GeometryPart74
import Snaky.E1GeometryPart75
import Snaky.E1GeometryPart76
import Snaky.E1GeometryPart77
import Snaky.E1GeometryPart78
import Snaky.E1GeometryPart79

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sources_complete_check : ((placements 10 10 snaky).filter eligible).all
    (fun F => sources.contains (traceOf F)) = true := by
  rw [Geometry10.placements_eq_targets]
  simp only [Geometry10.targets, List.filter_append, List.all_append, geometry00_checked, geometry01_checked, geometry02_checked, geometry03_checked, geometry04_checked, geometry05_checked, geometry06_checked, geometry07_checked, geometry08_checked, geometry09_checked, geometry10_checked, geometry11_checked, geometry12_checked, geometry13_checked, geometry14_checked, geometry15_checked, geometry16_checked, geometry17_checked, geometry18_checked, geometry19_checked, geometry20_checked, geometry21_checked, geometry22_checked, geometry23_checked, geometry24_checked, geometry25_checked, geometry26_checked, geometry27_checked, geometry28_checked, geometry29_checked, geometry30_checked, geometry31_checked, geometry32_checked, geometry33_checked, geometry34_checked, geometry35_checked, geometry36_checked, geometry37_checked, geometry38_checked, geometry39_checked, geometry40_checked, geometry41_checked, geometry42_checked, geometry43_checked, geometry44_checked, geometry45_checked, geometry46_checked, geometry47_checked, geometry48_checked, geometry49_checked, geometry50_checked, geometry51_checked, geometry52_checked, geometry53_checked, geometry54_checked, geometry55_checked, geometry56_checked, geometry57_checked, geometry58_checked, geometry59_checked, geometry60_checked, geometry61_checked, geometry62_checked, geometry63_checked, geometry64_checked, geometry65_checked, geometry66_checked, geometry67_checked, geometry68_checked, geometry69_checked, geometry70_checked, geometry71_checked, geometry72_checked, geometry73_checked, geometry74_checked, geometry75_checked, geometry76_checked, geometry77_checked, geometry78_checked, geometry79_checked, Bool.and_self]

theorem sources_complete {F : List Nat} (hF : F ∈ placements 10 10 snaky)
    (he : eligible F = true) : traceOf F ∈ sources := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp sources_complete_check F (List.mem_filter.mpr ⟨hF, he⟩))

theorem eligible_count : ((placements 10 10 snaky).filter eligible).length = 240 := by
  rw [Geometry10.placements_eq_targets]
  simp only [Geometry10.targets, List.filter_append, List.length_append, geometry00_count, geometry01_count, geometry02_count, geometry03_count, geometry04_count, geometry05_count, geometry06_count, geometry07_count, geometry08_count, geometry09_count, geometry10_count, geometry11_count, geometry12_count, geometry13_count, geometry14_count, geometry15_count, geometry16_count, geometry17_count, geometry18_count, geometry19_count, geometry20_count, geometry21_count, geometry22_count, geometry23_count, geometry24_count, geometry25_count, geometry26_count, geometry27_count, geometry28_count, geometry29_count, geometry30_count, geometry31_count, geometry32_count, geometry33_count, geometry34_count, geometry35_count, geometry36_count, geometry37_count, geometry38_count, geometry39_count, geometry40_count, geometry41_count, geometry42_count, geometry43_count, geometry44_count, geometry45_count, geometry46_count, geometry47_count, geometry48_count, geometry49_count, geometry50_count, geometry51_count, geometry52_count, geometry53_count, geometry54_count, geometry55_count, geometry56_count, geometry57_count, geometry58_count, geometry59_count, geometry60_count, geometry61_count, geometry62_count, geometry63_count, geometry64_count, geometry65_count, geometry66_count, geometry67_count, geometry68_count, geometry69_count, geometry70_count, geometry71_count, geometry72_count, geometry73_count, geometry74_count, geometry75_count, geometry76_count, geometry77_count, geometry78_count, geometry79_count]

theorem source_dimensions : (placements 10 10 snaky).length = 432 ∧
    ((placements 10 10 snaky).filter eligible).length = 240 ∧ sources.length = 240 :=
  ⟨Geometry10.target_count, eligible_count, by decide +kernel⟩

end Snaky.E1
