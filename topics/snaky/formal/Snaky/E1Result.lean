import Snaky.E1Geometry
import Snaky.E1ConfigCoverage
import Snaky.E1ConfigMatching
import Snaky.E1MaskInventory
import Snaky.E1Checks00
import Snaky.E1Checks01
import Snaky.E1Checks02
import Snaky.E1Checks03
import Snaky.E1Checks04
import Snaky.E1Checks05
import Snaky.E1Checks06
import Snaky.E1Checks07
import Snaky.E1Checks08
import Snaky.E1Checks09
import Snaky.E1Checks10
import Snaky.E1Checks11
import Snaky.E1Checks12
import Snaky.E1Checks13
import Snaky.E1Checks14

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def allMasks : List Nat := masks00 ++ masks01 ++ masks02 ++ masks03 ++ masks04 ++ masks05 ++ masks06 ++ masks07 ++ masks08 ++ masks09 ++ masks10 ++ masks11 ++ masks12 ++ masks13 ++ masks14
theorem validMasks_eq : validMasks = allMasks := by rw [validMasks_literal]; rfl
theorem validMasks_count : validMasks.length = 463 := by rw [validMasks_literal]; decide +kernel
theorem all_checked : validMasks.all checkMask = true := by
  rw [validMasks_eq]
  simp only [allMasks, List.all_append, masks00_checked, masks01_checked, masks02_checked, masks03_checked, masks04_checked, masks05_checked, masks06_checked, masks07_checked, masks08_checked, masks09_checked, masks10_checked, masks11_checked, masks12_checked, masks13_checked, masks14_checked, Bool.and_self]

theorem config_checked (mask mode : Nat) (hm : mask < 512)
    (hv : validRow mask = true) (hmode : mode < 3) :
    (sources.filter (fun t => !covered (config mask mode).pairs t)).all
      (rejected (config mask mode)) = true := by
  have hmask : mask ∈ validMasks := List.mem_filter.mpr ⟨List.mem_range.mpr hm, hv⟩
  have h := List.all_eq_true.mp all_checked mask hmask
  have hh := List.all_eq_true.mp h mode (List.mem_range.mpr hmode)
  change (sources.filter (fun t => !covered (pairsFor (phase mask) mode) t)).all _ = true
  rw [uncoveredFor_exact]
  exact hh

/-- Every active full eligible source is covered on the same entire core K.
The explicit membership constraints are hypotheses. This is not a claim
that all complete admissions satisfy them, or that the exterior is solved. -/
theorem e1_source_replacement (mask mode : Nat) (hm : mask < 512)
    (hv : validRow mask = true) (hmode : mode < 3)
    {K F : List Nat} (hc : Compatible (config mask mode) K)
    (hF : F ∈ placements 10 10 snaky) (he : eligible F = true)
    (hactive : (traceOf F).Subset K) :
    ∃ p ∈ (config mask mode).pairs,
      p.1 ∈ traceOf F ∧ p.2 ∈ traceOf F ∧ p.1 ∈ K ∧ p.2 ∈ K :=
  coverage_of_uncovered_check (config_checked mask mode hm hv hmode)
    hc (sources_complete hF he) hactive

/-- Any full-source incidence, including a different source, retains a pair. -/
theorem e1_physical_incidence_replacement (mask mode : Nat) (hm : mask < 512)
    (hv : validRow mask = true) (hmode : mode < 3)
    {K F E : List Nat} (hc : Compatible (config mask mode) K)
    (hF : F ∈ placements 10 10 snaky) (he : eligible F = true)
    (hactive : (traceOf F).Subset K) (hinc : (traceOf F).Subset E) :
    ∃ p ∈ (config mask mode).pairs,
      p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ∈ E ∧ p.2 ∈ E :=
  coverage_transfers (config_checked mask mode hm hv hmode)
    hc (sources_complete hF he) hactive hinc

end Snaky.E1
