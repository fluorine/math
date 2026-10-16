import Snaky.BreakerAdmission35Data
import Snaky.BreakerCoverage
import Snaky.Geometry10Data

namespace Snaky.BreakerAdmission35.G2
open Snaky.Breaker
def groupEntries : List Nat := [32,35,39,48,49]

private theorem mate32_0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker 32 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 32) breaker (outsideMate 32 x) ∧
    outsideMate 32 x ∉ P52.reserved ∧ outsideMate 32 x ≠ x ∧
    outsideMate 32 (outsideMate 32 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate32_20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker 32 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 32) breaker (outsideMate 32 x) ∧
    outsideMate 32 x ∉ P52.reserved ∧ outsideMate 32 x ≠ x ∧
    outsideMate 32 (outsideMate 32 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate32_40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker 32 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 32) breaker (outsideMate 32 x) ∧
    outsideMate 32 x ∉ P52.reserved ∧ outsideMate 32 x ≠ x ∧
    outsideMate 32 (outsideMate 32 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate32_60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker 32 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 32) breaker (outsideMate 32 x) ∧
    outsideMate 32 x ∉ P52.reserved ∧ outsideMate 32 x ≠ x ∧
    outsideMate 32 (outsideMate 32 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate32_80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker 32 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 32) breaker (outsideMate 32 x) ∧
    outsideMate 32 x ∉ P52.reserved ∧ outsideMate 32 x ≠ x ∧
    outsideMate 32 (outsideMate 32 x) = x := by
  unfold Fresh
  decide +kernel

private theorem matching32 : OuterOK 100 (maker 32) breaker P52.reserved (outsideMate 32) := by
  intro x hx hm hb hr
  have h100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact mate32_0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact mate32_20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact mate32_40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact mate32_60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  exact mate32_80 x (List.mem_range.mpr h100) (by omega) hm hb hr

private theorem mate35_0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker 35 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 35) breaker (outsideMate 35 x) ∧
    outsideMate 35 x ∉ P52.reserved ∧ outsideMate 35 x ≠ x ∧
    outsideMate 35 (outsideMate 35 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate35_20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker 35 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 35) breaker (outsideMate 35 x) ∧
    outsideMate 35 x ∉ P52.reserved ∧ outsideMate 35 x ≠ x ∧
    outsideMate 35 (outsideMate 35 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate35_40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker 35 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 35) breaker (outsideMate 35 x) ∧
    outsideMate 35 x ∉ P52.reserved ∧ outsideMate 35 x ≠ x ∧
    outsideMate 35 (outsideMate 35 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate35_60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker 35 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 35) breaker (outsideMate 35 x) ∧
    outsideMate 35 x ∉ P52.reserved ∧ outsideMate 35 x ≠ x ∧
    outsideMate 35 (outsideMate 35 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate35_80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker 35 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 35) breaker (outsideMate 35 x) ∧
    outsideMate 35 x ∉ P52.reserved ∧ outsideMate 35 x ≠ x ∧
    outsideMate 35 (outsideMate 35 x) = x := by
  unfold Fresh
  decide +kernel

private theorem matching35 : OuterOK 100 (maker 35) breaker P52.reserved (outsideMate 35) := by
  intro x hx hm hb hr
  have h100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact mate35_0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact mate35_20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact mate35_40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact mate35_60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  exact mate35_80 x (List.mem_range.mpr h100) (by omega) hm hb hr

private theorem mate39_0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker 39 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 39) breaker (outsideMate 39 x) ∧
    outsideMate 39 x ∉ P52.reserved ∧ outsideMate 39 x ≠ x ∧
    outsideMate 39 (outsideMate 39 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate39_20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker 39 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 39) breaker (outsideMate 39 x) ∧
    outsideMate 39 x ∉ P52.reserved ∧ outsideMate 39 x ≠ x ∧
    outsideMate 39 (outsideMate 39 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate39_40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker 39 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 39) breaker (outsideMate 39 x) ∧
    outsideMate 39 x ∉ P52.reserved ∧ outsideMate 39 x ≠ x ∧
    outsideMate 39 (outsideMate 39 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate39_60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker 39 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 39) breaker (outsideMate 39 x) ∧
    outsideMate 39 x ∉ P52.reserved ∧ outsideMate 39 x ≠ x ∧
    outsideMate 39 (outsideMate 39 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate39_80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker 39 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 39) breaker (outsideMate 39 x) ∧
    outsideMate 39 x ∉ P52.reserved ∧ outsideMate 39 x ≠ x ∧
    outsideMate 39 (outsideMate 39 x) = x := by
  unfold Fresh
  decide +kernel

private theorem matching39 : OuterOK 100 (maker 39) breaker P52.reserved (outsideMate 39) := by
  intro x hx hm hb hr
  have h100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact mate39_0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact mate39_20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact mate39_40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact mate39_60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  exact mate39_80 x (List.mem_range.mpr h100) (by omega) hm hb hr

private theorem mate48_0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker 48 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 48) breaker (outsideMate 48 x) ∧
    outsideMate 48 x ∉ P52.reserved ∧ outsideMate 48 x ≠ x ∧
    outsideMate 48 (outsideMate 48 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate48_20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker 48 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 48) breaker (outsideMate 48 x) ∧
    outsideMate 48 x ∉ P52.reserved ∧ outsideMate 48 x ≠ x ∧
    outsideMate 48 (outsideMate 48 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate48_40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker 48 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 48) breaker (outsideMate 48 x) ∧
    outsideMate 48 x ∉ P52.reserved ∧ outsideMate 48 x ≠ x ∧
    outsideMate 48 (outsideMate 48 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate48_60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker 48 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 48) breaker (outsideMate 48 x) ∧
    outsideMate 48 x ∉ P52.reserved ∧ outsideMate 48 x ≠ x ∧
    outsideMate 48 (outsideMate 48 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate48_80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker 48 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 48) breaker (outsideMate 48 x) ∧
    outsideMate 48 x ∉ P52.reserved ∧ outsideMate 48 x ≠ x ∧
    outsideMate 48 (outsideMate 48 x) = x := by
  unfold Fresh
  decide +kernel

private theorem matching48 : OuterOK 100 (maker 48) breaker P52.reserved (outsideMate 48) := by
  intro x hx hm hb hr
  have h100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact mate48_0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact mate48_20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact mate48_40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact mate48_60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  exact mate48_80 x (List.mem_range.mpr h100) (by omega) hm hb hr

private theorem mate49_0 : ∀ x ∈ List.range 20, 0 ≤ x →
    x ∉ maker 49 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 49) breaker (outsideMate 49 x) ∧
    outsideMate 49 x ∉ P52.reserved ∧ outsideMate 49 x ≠ x ∧
    outsideMate 49 (outsideMate 49 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate49_20 : ∀ x ∈ List.range 40, 20 ≤ x →
    x ∉ maker 49 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 49) breaker (outsideMate 49 x) ∧
    outsideMate 49 x ∉ P52.reserved ∧ outsideMate 49 x ≠ x ∧
    outsideMate 49 (outsideMate 49 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate49_40 : ∀ x ∈ List.range 60, 40 ≤ x →
    x ∉ maker 49 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 49) breaker (outsideMate 49 x) ∧
    outsideMate 49 x ∉ P52.reserved ∧ outsideMate 49 x ≠ x ∧
    outsideMate 49 (outsideMate 49 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate49_60 : ∀ x ∈ List.range 80, 60 ≤ x →
    x ∉ maker 49 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 49) breaker (outsideMate 49 x) ∧
    outsideMate 49 x ∉ P52.reserved ∧ outsideMate 49 x ≠ x ∧
    outsideMate 49 (outsideMate 49 x) = x := by
  unfold Fresh
  decide +kernel

private theorem mate49_80 : ∀ x ∈ List.range 100, 80 ≤ x →
    x ∉ maker 49 → x ∉ breaker → x ∉ P52.reserved →
    Fresh 100 (maker 49) breaker (outsideMate 49 x) ∧
    outsideMate 49 x ∉ P52.reserved ∧ outsideMate 49 x ≠ x ∧
    outsideMate 49 (outsideMate 49 x) = x := by
  unfold Fresh
  decide +kernel

private theorem matching49 : OuterOK 100 (maker 49) breaker P52.reserved (outsideMate 49) := by
  intro x hx hm hb hr
  have h100 : x < 100 := List.mem_range.mp hx
  by_cases h20 : x < 20
  · exact mate49_0 x (List.mem_range.mpr h20) (by omega) hm hb hr
  by_cases h40 : x < 40
  · exact mate49_20 x (List.mem_range.mpr h40) (by omega) hm hb hr
  by_cases h60 : x < 60
  · exact mate49_40 x (List.mem_range.mpr h60) (by omega) hm hb hr
  by_cases h80 : x < 80
  · exact mate49_60 x (List.mem_range.mpr h80) (by omega) hm hb hr
  exact mate49_80 x (List.mem_range.mpr h100) (by omega) hm hb hr

theorem matching : ∀ u ∈ groupEntries, OuterOK 100 (maker u) breaker P52.reserved (outsideMate u) := by
  intro u hu
  have cases : u = 32 ∨ u = 35 ∨ u = 39 ∨ u = 48 ∨ u = 49 := by
    simpa only [groupEntries,List.mem_cons,List.not_mem_nil,or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact matching32
  · exact matching35
  · exact matching39
  · exact matching48
  · exact matching49

private theorem cover00 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part00 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover01 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part01 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover02 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part02 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover03 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part03 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover04 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part04 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover05 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part05 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover06 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part06 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover07 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part07 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover08 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part08 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover09 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part09 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover10 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part10 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover11 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part11 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover12 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part12 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover13 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part13 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover14 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part14 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover15 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part15 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover16 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part16 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover17 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part17 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover18 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part18 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover19 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part19 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover20 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part20 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover21 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part21 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover22 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part22 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover23 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part23 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover24 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part24 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover25 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part25 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover26 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part26 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover27 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part27 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover28 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part28 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover29 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part29 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover30 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part30 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover31 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part31 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover32 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part32 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover33 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part33 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover34 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part34 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover35 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part35 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover36 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part36 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover37 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part37 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover38 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part38 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover39 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part39 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover40 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part40 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover41 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part41 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover42 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part42 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover43 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part43 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover44 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part44 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover45 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part45 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover46 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part46 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover47 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part47 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover48 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part48 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover49 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part49 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover50 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part50 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover51 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part51 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover52 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part52 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover53 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part53 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover54 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part54 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover55 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part55 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover56 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part56 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover57 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part57 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover58 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part58 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover59 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part59 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover60 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part60 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover61 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part61 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover62 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part62 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover63 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part63 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover64 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part64 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover65 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part65 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover66 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part66 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover67 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part67 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover68 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part68 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover69 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part69 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover70 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part70 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover71 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part71 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover72 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part72 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover73 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part73 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover74 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part74 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover75 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part75 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover76 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part76 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover77 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part77 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover78 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part78 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

private theorem cover79 : ∀ u ∈ groupEntries,
    WaitingCovers Geometry10.part79 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  unfold WaitingCovers OuterDomain Fresh
  decide +kernel

theorem literal_coverage (u : Nat) (hu : u ∈ groupEntries) :
    WaitingCovers Geometry10.targets 100 (maker u) breaker P52.reserved P52.guards (outsideMate u) := by
  simpa only [Geometry10.targets,List.append_assoc] using (waitingCovers_append (cover00 u hu) (waitingCovers_append (cover01 u hu) (waitingCovers_append (cover02 u hu) (waitingCovers_append (cover03 u hu) (waitingCovers_append (cover04 u hu) (waitingCovers_append (cover05 u hu) (waitingCovers_append (cover06 u hu) (waitingCovers_append (cover07 u hu) (waitingCovers_append (cover08 u hu) (waitingCovers_append (cover09 u hu) (waitingCovers_append (cover10 u hu) (waitingCovers_append (cover11 u hu) (waitingCovers_append (cover12 u hu) (waitingCovers_append (cover13 u hu) (waitingCovers_append (cover14 u hu) (waitingCovers_append (cover15 u hu) (waitingCovers_append (cover16 u hu) (waitingCovers_append (cover17 u hu) (waitingCovers_append (cover18 u hu) (waitingCovers_append (cover19 u hu) (waitingCovers_append (cover20 u hu) (waitingCovers_append (cover21 u hu) (waitingCovers_append (cover22 u hu) (waitingCovers_append (cover23 u hu) (waitingCovers_append (cover24 u hu) (waitingCovers_append (cover25 u hu) (waitingCovers_append (cover26 u hu) (waitingCovers_append (cover27 u hu) (waitingCovers_append (cover28 u hu) (waitingCovers_append (cover29 u hu) (waitingCovers_append (cover30 u hu) (waitingCovers_append (cover31 u hu) (waitingCovers_append (cover32 u hu) (waitingCovers_append (cover33 u hu) (waitingCovers_append (cover34 u hu) (waitingCovers_append (cover35 u hu) (waitingCovers_append (cover36 u hu) (waitingCovers_append (cover37 u hu) (waitingCovers_append (cover38 u hu) (waitingCovers_append (cover39 u hu) (waitingCovers_append (cover40 u hu) (waitingCovers_append (cover41 u hu) (waitingCovers_append (cover42 u hu) (waitingCovers_append (cover43 u hu) (waitingCovers_append (cover44 u hu) (waitingCovers_append (cover45 u hu) (waitingCovers_append (cover46 u hu) (waitingCovers_append (cover47 u hu) (waitingCovers_append (cover48 u hu) (waitingCovers_append (cover49 u hu) (waitingCovers_append (cover50 u hu) (waitingCovers_append (cover51 u hu) (waitingCovers_append (cover52 u hu) (waitingCovers_append (cover53 u hu) (waitingCovers_append (cover54 u hu) (waitingCovers_append (cover55 u hu) (waitingCovers_append (cover56 u hu) (waitingCovers_append (cover57 u hu) (waitingCovers_append (cover58 u hu) (waitingCovers_append (cover59 u hu) (waitingCovers_append (cover60 u hu) (waitingCovers_append (cover61 u hu) (waitingCovers_append (cover62 u hu) (waitingCovers_append (cover63 u hu) (waitingCovers_append (cover64 u hu) (waitingCovers_append (cover65 u hu) (waitingCovers_append (cover66 u hu) (waitingCovers_append (cover67 u hu) (waitingCovers_append (cover68 u hu) (waitingCovers_append (cover69 u hu) (waitingCovers_append (cover70 u hu) (waitingCovers_append (cover71 u hu) (waitingCovers_append (cover72 u hu) (waitingCovers_append (cover73 u hu) (waitingCovers_append (cover74 u hu) (waitingCovers_append (cover75 u hu) (waitingCovers_append (cover76 u hu) (waitingCovers_append (cover77 u hu) (waitingCovers_append (cover78 u hu) (cover79 u hu))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Snaky.BreakerAdmission35.G2
