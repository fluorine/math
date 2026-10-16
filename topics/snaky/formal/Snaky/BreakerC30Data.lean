import Snaky.BreakerComponent

/-! Twelve complete conditional physical defenses after Mz/B43.
The original 9+9 colors, full domains and both local controllers
are explicit. The original C30 root is not a theorem here. -/
namespace Snaky.BreakerC30
open Snaky.Breaker

def maker₀ : List Nat := [37,44,45,46,47,57,67,75,84]
def breaker : List Nat := [34,36,38,43,55,56,58,74,77,94]
def entries : List Nat := [0,2,7,20,39,48,69,87,90,97,98,99]

namespace R
def domain : List Nat := [16,17,18,26,27,28]
def guards : List (List Nat) := [[16,17,18],[16,17,26],[16,17,27],[16,26,27],[17,18,27],[18,27,28]]
def reply : Nat → Nat
  | 16 => 17
  | 17 => 16
  | 18 => 27
  | 26 => 27
  | 27 => 17
  | 28 => 27
  | u => u
def localPairs : Nat → List (Nat × Nat)
  | 16 => [(26,27),(18,28)]
  | 17 => [(18,27)]
  | 18 => [(16,17)]
  | 26 => [(16,17)]
  | 27 => [(16,26),(18,28)]
  | 28 => [(16,17)]
  | _ => []
def localDomain (u : Nat) : List Nat := (localPairs u).flatMap (fun p => [p.1,p.2])
def localMate (u : Nat) := mateOfPairs (localPairs u)
theorem shape : GuardOK domain guards := by
  unfold GuardOK
  decide +kernel

private theorem row16 :
    Fresh 100 [16] (outside 100 domain) (reply 16) ∧
    PartialOK 100 [16] (reply 16 :: outside 100 domain) (localDomain 16) (localMate 16) ∧
    PartialCovers guards [16] (reply 16 :: outside 100 domain) (localDomain 16) (localMate 16) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row17 :
    Fresh 100 [17] (outside 100 domain) (reply 17) ∧
    PartialOK 100 [17] (reply 17 :: outside 100 domain) (localDomain 17) (localMate 17) ∧
    PartialCovers guards [17] (reply 17 :: outside 100 domain) (localDomain 17) (localMate 17) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row18 :
    Fresh 100 [18] (outside 100 domain) (reply 18) ∧
    PartialOK 100 [18] (reply 18 :: outside 100 domain) (localDomain 18) (localMate 18) ∧
    PartialCovers guards [18] (reply 18 :: outside 100 domain) (localDomain 18) (localMate 18) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row26 :
    Fresh 100 [26] (outside 100 domain) (reply 26) ∧
    PartialOK 100 [26] (reply 26 :: outside 100 domain) (localDomain 26) (localMate 26) ∧
    PartialCovers guards [26] (reply 26 :: outside 100 domain) (localDomain 26) (localMate 26) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row27 :
    Fresh 100 [27] (outside 100 domain) (reply 27) ∧
    PartialOK 100 [27] (reply 27 :: outside 100 domain) (localDomain 27) (localMate 27) ∧
    PartialCovers guards [27] (reply 27 :: outside 100 domain) (localDomain 27) (localMate 27) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row28 :
    Fresh 100 [28] (outside 100 domain) (reply 28) ∧
    PartialOK 100 [28] (reply 28 :: outside 100 domain) (localDomain 28) (localMate 28) ∧
    PartialCovers guards [28] (reply 28 :: outside 100 domain) (localDomain 28) (localMate 28) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

theorem rows : LocalReplyOK guards 100 domain reply localDomain localMate := by
  intro u hu
  have cases : u = 16 ∨ u = 17 ∨ u = 18 ∨ u = 26 ∨ u = 27 ∨ u = 28 := by
    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row16
  · exact row17
  · exact row18
  · exact row26
  · exact row27
  · exact row28
theorem defense : ¬ BlackWins guards 100 [] (outside 100 domain) :=
  local_reply_not_blackWins shape rows
end R

namespace T
def domain : List Nat := [10,11,12,13,14,15,21,22,23,24,25,33,35]
def guards : List (List Nat) := [[11,12,13],[12,13,23,24,25],[13,14,21,22,23],[13,14,24,25],[14,15],[15,25,35],[21,22,23,24],[22,23,24,25],[23,24,33]]
def reply : Nat → Nat
  | 10 => 14
  | 11 => 14
  | 12 => 15
  | 13 => 15
  | 14 => 15
  | 15 => 14
  | 21 => 15
  | 22 => 15
  | 23 => 25
  | 24 => 25
  | 25 => 15
  | 33 => 15
  | 35 => 14
  | u => u
def localPairs : Nat → List (Nat × Nat)
  | 10 => [(12,13),(15,25),(22,23),(24,33)]
  | 11 => [(12,13),(15,25),(22,23),(24,33)]
  | 12 => [(11,13),(23,24),(14,25),(21,22)]
  | 13 => [(11,12),(21,22),(23,33),(24,25)]
  | 14 => [(11,12),(21,22),(23,33),(24,25)]
  | 15 => [(12,13),(23,24),(25,35)]
  | 21 => [(11,12),(13,14),(23,24)]
  | 22 => [(11,12),(13,14),(23,24)]
  | 23 => [(11,12),(14,15),(21,22),(24,33)]
  | 24 => [(11,12),(14,15),(21,22),(23,33)]
  | 25 => [(11,12),(13,14),(23,24)]
  | 33 => [(11,12),(13,14),(23,24)]
  | 35 => [(12,13),(15,25),(22,23),(24,33)]
  | _ => []
def localDomain (u : Nat) : List Nat := (localPairs u).flatMap (fun p => [p.1,p.2])
def localMate (u : Nat) := mateOfPairs (localPairs u)
theorem shape : GuardOK domain guards := by
  unfold GuardOK
  decide +kernel

private theorem row10 :
    Fresh 100 [10] (outside 100 domain) (reply 10) ∧
    PartialOK 100 [10] (reply 10 :: outside 100 domain) (localDomain 10) (localMate 10) ∧
    PartialCovers guards [10] (reply 10 :: outside 100 domain) (localDomain 10) (localMate 10) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row11 :
    Fresh 100 [11] (outside 100 domain) (reply 11) ∧
    PartialOK 100 [11] (reply 11 :: outside 100 domain) (localDomain 11) (localMate 11) ∧
    PartialCovers guards [11] (reply 11 :: outside 100 domain) (localDomain 11) (localMate 11) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row12 :
    Fresh 100 [12] (outside 100 domain) (reply 12) ∧
    PartialOK 100 [12] (reply 12 :: outside 100 domain) (localDomain 12) (localMate 12) ∧
    PartialCovers guards [12] (reply 12 :: outside 100 domain) (localDomain 12) (localMate 12) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row13 :
    Fresh 100 [13] (outside 100 domain) (reply 13) ∧
    PartialOK 100 [13] (reply 13 :: outside 100 domain) (localDomain 13) (localMate 13) ∧
    PartialCovers guards [13] (reply 13 :: outside 100 domain) (localDomain 13) (localMate 13) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row14 :
    Fresh 100 [14] (outside 100 domain) (reply 14) ∧
    PartialOK 100 [14] (reply 14 :: outside 100 domain) (localDomain 14) (localMate 14) ∧
    PartialCovers guards [14] (reply 14 :: outside 100 domain) (localDomain 14) (localMate 14) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row15 :
    Fresh 100 [15] (outside 100 domain) (reply 15) ∧
    PartialOK 100 [15] (reply 15 :: outside 100 domain) (localDomain 15) (localMate 15) ∧
    PartialCovers guards [15] (reply 15 :: outside 100 domain) (localDomain 15) (localMate 15) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row21 :
    Fresh 100 [21] (outside 100 domain) (reply 21) ∧
    PartialOK 100 [21] (reply 21 :: outside 100 domain) (localDomain 21) (localMate 21) ∧
    PartialCovers guards [21] (reply 21 :: outside 100 domain) (localDomain 21) (localMate 21) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row22 :
    Fresh 100 [22] (outside 100 domain) (reply 22) ∧
    PartialOK 100 [22] (reply 22 :: outside 100 domain) (localDomain 22) (localMate 22) ∧
    PartialCovers guards [22] (reply 22 :: outside 100 domain) (localDomain 22) (localMate 22) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row23 :
    Fresh 100 [23] (outside 100 domain) (reply 23) ∧
    PartialOK 100 [23] (reply 23 :: outside 100 domain) (localDomain 23) (localMate 23) ∧
    PartialCovers guards [23] (reply 23 :: outside 100 domain) (localDomain 23) (localMate 23) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row24 :
    Fresh 100 [24] (outside 100 domain) (reply 24) ∧
    PartialOK 100 [24] (reply 24 :: outside 100 domain) (localDomain 24) (localMate 24) ∧
    PartialCovers guards [24] (reply 24 :: outside 100 domain) (localDomain 24) (localMate 24) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row25 :
    Fresh 100 [25] (outside 100 domain) (reply 25) ∧
    PartialOK 100 [25] (reply 25 :: outside 100 domain) (localDomain 25) (localMate 25) ∧
    PartialCovers guards [25] (reply 25 :: outside 100 domain) (localDomain 25) (localMate 25) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row33 :
    Fresh 100 [33] (outside 100 domain) (reply 33) ∧
    PartialOK 100 [33] (reply 33 :: outside 100 domain) (localDomain 33) (localMate 33) ∧
    PartialCovers guards [33] (reply 33 :: outside 100 domain) (localDomain 33) (localMate 33) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

private theorem row35 :
    Fresh 100 [35] (outside 100 domain) (reply 35) ∧
    PartialOK 100 [35] (reply 35 :: outside 100 domain) (localDomain 35) (localMate 35) ∧
    PartialCovers guards [35] (reply 35 :: outside 100 domain) (localDomain 35) (localMate 35) := by
  unfold PartialOK PartialCovers Fresh
  decide +kernel

theorem rows : LocalReplyOK guards 100 domain reply localDomain localMate := by
  intro u hu
  have cases : u = 10 ∨ u = 11 ∨ u = 12 ∨ u = 13 ∨ u = 14 ∨ u = 15 ∨ u = 21 ∨ u = 22 ∨ u = 23 ∨ u = 24 ∨ u = 25 ∨ u = 33 ∨ u = 35 := by
    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row33
  · exact row35
theorem defense : ¬ BlackWins guards 100 [] (outside 100 domain) :=
  local_reply_not_blackWins shape rows
end T

def domains : Nat → List Nat
  | 0 => [1,3]
  | 1 => [4,5]
  | 2 => [6,19]
  | 3 => [8,9]
  | 4 => [29,49]
  | 5 => [59,79]
  | 6 => [60,80]
  | 7 => [64,65]
  | 8 => [66,76]
  | 9 => [68,78]
  | 10 => [70,71]
  | 11 => [81,91]
  | 12 => [82,83]
  | 13 => [85,86]
  | 14 => [88,89]
  | 15 => [92,93]
  | 16 => [95,96]
  | 17 => [30,40]
  | 18 => [31,41]
  | 19 => [32,42]
  | 20 => [50,52]
  | 21 => [51,61]
  | 22 => [53,54]
  | 23 => [62,72]
  | 24 => [63,73]
  | 25 => R.domain
  | 26 => T.domain
  | _ => []
def targets : Nat → List (List Nat)
  | 0 => [[1,3]]
  | 1 => [[4,5]]
  | 2 => [[6,19]]
  | 3 => [[8,9]]
  | 4 => [[29,49]]
  | 5 => [[59,79]]
  | 6 => [[60,80]]
  | 7 => [[64,65]]
  | 8 => [[66,76]]
  | 9 => [[68,78]]
  | 10 => [[70,71]]
  | 11 => [[81,91]]
  | 12 => [[82,83]]
  | 13 => [[85,86]]
  | 14 => [[88,89]]
  | 15 => [[92,93]]
  | 16 => [[95,96]]
  | 17 => [[30,40]]
  | 18 => [[31,41]]
  | 19 => [[32,42]]
  | 20 => [[50,52]]
  | 21 => [[51,61]]
  | 22 => [[53,54]]
  | 23 => [[62,72]]
  | 24 => [[63,73]]
  | 25 => R.guards
  | 26 => T.guards
  | _ => []

theorem colors_disjoint : ∀ z ∈ entries, Disjoint (z :: maker₀) breaker := by
  unfold Disjoint
  decide +kernel

theorem shapes : ∀ i ∈ List.range 27, GuardOK (domains i) (targets i) := by
  unfold GuardOK
  decide +kernel

private theorem fresh0 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (0 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh2 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (2 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh7 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (7 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh20 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (20 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh39 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (39 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh48 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (48 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh69 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (69 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh87 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (87 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh90 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (90 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh97 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (97 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh98 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (98 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

private theorem fresh99 : ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (99 :: maker₀) breaker x := by
  unfold Fresh
  decide +kernel

theorem fresh_domains : ∀ z ∈ entries, ∀ i ∈ List.range 27, ∀ x ∈ domains i,
    Fresh 100 (z :: maker₀) breaker x := by
  intro z hz
  have cases : z = 0 ∨ z = 2 ∨ z = 7 ∨ z = 20 ∨ z = 39 ∨ z = 48 ∨ z = 69 ∨ z = 87 ∨ z = 90 ∨ z = 97 ∨ z = 98 ∨ z = 99 := by
    simpa only [entries, List.mem_cons, List.not_mem_nil, or_false] using hz
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fresh0
  · exact fresh2
  · exact fresh7
  · exact fresh20
  · exact fresh39
  · exact fresh48
  · exact fresh69
  · exact fresh87
  · exact fresh90
  · exact fresh97
  · exact fresh98
  · exact fresh99

private theorem disjoint0 : ∀ j ∈ List.range 27, 0 ≠ j →
    ∀ x ∈ domains 0, x ∉ domains j := by
  decide +kernel

private theorem disjoint1 : ∀ j ∈ List.range 27, 1 ≠ j →
    ∀ x ∈ domains 1, x ∉ domains j := by
  decide +kernel

private theorem disjoint2 : ∀ j ∈ List.range 27, 2 ≠ j →
    ∀ x ∈ domains 2, x ∉ domains j := by
  decide +kernel

private theorem disjoint3 : ∀ j ∈ List.range 27, 3 ≠ j →
    ∀ x ∈ domains 3, x ∉ domains j := by
  decide +kernel

private theorem disjoint4 : ∀ j ∈ List.range 27, 4 ≠ j →
    ∀ x ∈ domains 4, x ∉ domains j := by
  decide +kernel

private theorem disjoint5 : ∀ j ∈ List.range 27, 5 ≠ j →
    ∀ x ∈ domains 5, x ∉ domains j := by
  decide +kernel

private theorem disjoint6 : ∀ j ∈ List.range 27, 6 ≠ j →
    ∀ x ∈ domains 6, x ∉ domains j := by
  decide +kernel

private theorem disjoint7 : ∀ j ∈ List.range 27, 7 ≠ j →
    ∀ x ∈ domains 7, x ∉ domains j := by
  decide +kernel

private theorem disjoint8 : ∀ j ∈ List.range 27, 8 ≠ j →
    ∀ x ∈ domains 8, x ∉ domains j := by
  decide +kernel

private theorem disjoint9 : ∀ j ∈ List.range 27, 9 ≠ j →
    ∀ x ∈ domains 9, x ∉ domains j := by
  decide +kernel

private theorem disjoint10 : ∀ j ∈ List.range 27, 10 ≠ j →
    ∀ x ∈ domains 10, x ∉ domains j := by
  decide +kernel

private theorem disjoint11 : ∀ j ∈ List.range 27, 11 ≠ j →
    ∀ x ∈ domains 11, x ∉ domains j := by
  decide +kernel

private theorem disjoint12 : ∀ j ∈ List.range 27, 12 ≠ j →
    ∀ x ∈ domains 12, x ∉ domains j := by
  decide +kernel

private theorem disjoint13 : ∀ j ∈ List.range 27, 13 ≠ j →
    ∀ x ∈ domains 13, x ∉ domains j := by
  decide +kernel

private theorem disjoint14 : ∀ j ∈ List.range 27, 14 ≠ j →
    ∀ x ∈ domains 14, x ∉ domains j := by
  decide +kernel

private theorem disjoint15 : ∀ j ∈ List.range 27, 15 ≠ j →
    ∀ x ∈ domains 15, x ∉ domains j := by
  decide +kernel

private theorem disjoint16 : ∀ j ∈ List.range 27, 16 ≠ j →
    ∀ x ∈ domains 16, x ∉ domains j := by
  decide +kernel

private theorem disjoint17 : ∀ j ∈ List.range 27, 17 ≠ j →
    ∀ x ∈ domains 17, x ∉ domains j := by
  decide +kernel

private theorem disjoint18 : ∀ j ∈ List.range 27, 18 ≠ j →
    ∀ x ∈ domains 18, x ∉ domains j := by
  decide +kernel

private theorem disjoint19 : ∀ j ∈ List.range 27, 19 ≠ j →
    ∀ x ∈ domains 19, x ∉ domains j := by
  decide +kernel

private theorem disjoint20 : ∀ j ∈ List.range 27, 20 ≠ j →
    ∀ x ∈ domains 20, x ∉ domains j := by
  decide +kernel

private theorem disjoint21 : ∀ j ∈ List.range 27, 21 ≠ j →
    ∀ x ∈ domains 21, x ∉ domains j := by
  decide +kernel

private theorem disjoint22 : ∀ j ∈ List.range 27, 22 ≠ j →
    ∀ x ∈ domains 22, x ∉ domains j := by
  decide +kernel

private theorem disjoint23 : ∀ j ∈ List.range 27, 23 ≠ j →
    ∀ x ∈ domains 23, x ∉ domains j := by
  decide +kernel

private theorem disjoint24 : ∀ j ∈ List.range 27, 24 ≠ j →
    ∀ x ∈ domains 24, x ∉ domains j := by
  decide +kernel

private theorem disjoint25 : ∀ j ∈ List.range 27, 25 ≠ j →
    ∀ x ∈ domains 25, x ∉ domains j := by
  decide +kernel

private theorem disjoint26 : ∀ j ∈ List.range 27, 26 ≠ j →
    ∀ x ∈ domains 26, x ∉ domains j := by
  decide +kernel

theorem disjoint_domains : DomainsDisjoint 27 domains := by
  intro i hi
  have hiN : i < 27 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact disjoint0
  · exact disjoint1
  · exact disjoint2
  · exact disjoint3
  · exact disjoint4
  · exact disjoint5
  · exact disjoint6
  · exact disjoint7
  · exact disjoint8
  · exact disjoint9
  · exact disjoint10
  · exact disjoint11
  · exact disjoint12
  · exact disjoint13
  · exact disjoint14
  · exact disjoint15
  · exact disjoint16
  · exact disjoint17
  · exact disjoint18
  · exact disjoint19
  · exact disjoint20
  · exact disjoint21
  · exact disjoint22
  · exact disjoint23
  · exact disjoint24
  · exact disjoint25
  · exact disjoint26

theorem component_defenses : ∀ i ∈ List.range 27,
    ¬ BlackWins (targets i) 100 [] (outside 100 (domains i)) := by
  intro i hi
  have hiN : i < 27 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 100) (a := 1) (b := 3) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 4) (b := 5) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 6) (b := 19) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 8) (b := 9) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 29) (b := 49) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 59) (b := 79) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 60) (b := 80) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 64) (b := 65) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 66) (b := 76) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 68) (b := 78) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 70) (b := 71) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 81) (b := 91) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 82) (b := 83) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 85) (b := 86) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 88) (b := 89) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 92) (b := 93) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 95) (b := 96) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 30) (b := 40) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 31) (b := 41) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 32) (b := 42) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 50) (b := 52) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 51) (b := 61) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 53) (b := 54) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 62) (b := 72) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 100) (a := 63) (b := 73) (by decide) (by decide) (by decide)
  · exact R.defense
  · exact T.defense

end Snaky.BreakerC30
