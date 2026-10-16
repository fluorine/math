import Snaky.BreakerN32Context00

namespace Snaky.BreakerN32
open Snaky.Breaker
def maker : List Nat := [48,49,51,60,61,62,66,75,76,77,79,82,88,90,93,102,103,104,105,106,107,116,121,129,130,133,135,136,137,147,148,149]
def breaker : List Nat := [25,34,35,47,50,59,63,65,74,78,80,87,89,91,92,94,101,115,117,118,119,120,122,131,134,138,143,144,146,150,162,164]
private def rootDomains : Nat → List Nat
  | 0 => [0,14]
  | 1 => [1,56]
  | 2 => [2,4]
  | 3 => [3,17]
  | 4 => [5,6]
  | 5 => [7,8]
  | 6 => [9,37]
  | 7 => [10,20]
  | 8 => [11,12]
  | 9 => [15,16]
  | 10 => [18,19]
  | 11 => [21,22]
  | 12 => [23,24]
  | 13 => [28,45]
  | 14 => [29,70]
  | 15 => [30,31]
  | 16 => [32,46]
  | 17 => [38,39]
  | 18 => [42,85]
  | 19 => [43,44]
  | 20 => [57,71]
  | 21 => [58,72]
  | 22 => [84,98]
  | 23 => [86,100]
  | 24 => [99,113]
  | 25 => [112,126]
  | 26 => [114,142]
  | 27 => [127,128]
  | 28 => [140,168]
  | 29 => [141,155]
  | 30 => [151,165]
  | 31 => [152,166]
  | 32 => [153,167]
  | 33 => [156,170]
  | 34 => [157,158]
  | 35 => [159,160]
  | 36 => [161,188]
  | 37 => [163,177]
  | 38 => [171,172]
  | 39 => [175,176]
  | 40 => [178,179]
  | 41 => [180,191]
  | 42 => [181,194]
  | 43 => [185,186]
  | 44 => [189,190]
  | 45 => [192,193]
  | 46 => C00.domain
  | _ => []
private def rootTargets : Nat → List (List Nat)
  | 0 => [[0,14]]
  | 1 => [[1,56]]
  | 2 => [[2,4]]
  | 3 => [[3,17]]
  | 4 => [[5,6]]
  | 5 => [[7,8]]
  | 6 => [[9,37]]
  | 7 => [[10,20]]
  | 8 => [[11,12]]
  | 9 => [[15,16]]
  | 10 => [[18,19]]
  | 11 => [[21,22]]
  | 12 => [[23,24]]
  | 13 => [[28,45]]
  | 14 => [[29,70]]
  | 15 => [[30,31]]
  | 16 => [[32,46]]
  | 17 => [[38,39]]
  | 18 => [[42,85]]
  | 19 => [[43,44]]
  | 20 => [[57,71]]
  | 21 => [[58,72]]
  | 22 => [[84,98]]
  | 23 => [[86,100]]
  | 24 => [[99,113]]
  | 25 => [[112,126]]
  | 26 => [[114,142]]
  | 27 => [[127,128]]
  | 28 => [[140,168]]
  | 29 => [[141,155]]
  | 30 => [[151,165]]
  | 31 => [[152,166]]
  | 32 => [[153,167]]
  | 33 => [[156,170]]
  | 34 => [[157,158]]
  | 35 => [[159,160]]
  | 36 => [[161,188]]
  | 37 => [[163,177]]
  | 38 => [[171,172]]
  | 39 => [[175,176]]
  | 40 => [[178,179]]
  | 41 => [[180,191]]
  | 42 => [[181,194]]
  | 43 => [[185,186]]
  | 44 => [[189,190]]
  | 45 => [[192,193]]
  | 46 => C00.guards
  | _ => []
def domains := rootDomains
def targets := rootTargets
theorem colors_disjoint : Disjoint maker breaker := by
  unfold Disjoint
  decide +kernel
theorem shapes : ∀ i ∈ List.range 47, GuardOK (domains i) (targets i) := by
  unfold GuardOK
  decide +kernel
private theorem fresh0 : ∀ x ∈ domains 0, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint0 : ∀ j ∈ List.range 47, 0 ≠ j →
    ∀ x ∈ domains 0, x ∉ domains j := by
  decide +kernel
private theorem fresh1 : ∀ x ∈ domains 1, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint1 : ∀ j ∈ List.range 47, 1 ≠ j →
    ∀ x ∈ domains 1, x ∉ domains j := by
  decide +kernel
private theorem fresh2 : ∀ x ∈ domains 2, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint2 : ∀ j ∈ List.range 47, 2 ≠ j →
    ∀ x ∈ domains 2, x ∉ domains j := by
  decide +kernel
private theorem fresh3 : ∀ x ∈ domains 3, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint3 : ∀ j ∈ List.range 47, 3 ≠ j →
    ∀ x ∈ domains 3, x ∉ domains j := by
  decide +kernel
private theorem fresh4 : ∀ x ∈ domains 4, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint4 : ∀ j ∈ List.range 47, 4 ≠ j →
    ∀ x ∈ domains 4, x ∉ domains j := by
  decide +kernel
private theorem fresh5 : ∀ x ∈ domains 5, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint5 : ∀ j ∈ List.range 47, 5 ≠ j →
    ∀ x ∈ domains 5, x ∉ domains j := by
  decide +kernel
private theorem fresh6 : ∀ x ∈ domains 6, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint6 : ∀ j ∈ List.range 47, 6 ≠ j →
    ∀ x ∈ domains 6, x ∉ domains j := by
  decide +kernel
private theorem fresh7 : ∀ x ∈ domains 7, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint7 : ∀ j ∈ List.range 47, 7 ≠ j →
    ∀ x ∈ domains 7, x ∉ domains j := by
  decide +kernel
private theorem fresh8 : ∀ x ∈ domains 8, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint8 : ∀ j ∈ List.range 47, 8 ≠ j →
    ∀ x ∈ domains 8, x ∉ domains j := by
  decide +kernel
private theorem fresh9 : ∀ x ∈ domains 9, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint9 : ∀ j ∈ List.range 47, 9 ≠ j →
    ∀ x ∈ domains 9, x ∉ domains j := by
  decide +kernel
private theorem fresh10 : ∀ x ∈ domains 10, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint10 : ∀ j ∈ List.range 47, 10 ≠ j →
    ∀ x ∈ domains 10, x ∉ domains j := by
  decide +kernel
private theorem fresh11 : ∀ x ∈ domains 11, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint11 : ∀ j ∈ List.range 47, 11 ≠ j →
    ∀ x ∈ domains 11, x ∉ domains j := by
  decide +kernel
private theorem fresh12 : ∀ x ∈ domains 12, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint12 : ∀ j ∈ List.range 47, 12 ≠ j →
    ∀ x ∈ domains 12, x ∉ domains j := by
  decide +kernel
private theorem fresh13 : ∀ x ∈ domains 13, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint13 : ∀ j ∈ List.range 47, 13 ≠ j →
    ∀ x ∈ domains 13, x ∉ domains j := by
  decide +kernel
private theorem fresh14 : ∀ x ∈ domains 14, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint14 : ∀ j ∈ List.range 47, 14 ≠ j →
    ∀ x ∈ domains 14, x ∉ domains j := by
  decide +kernel
private theorem fresh15 : ∀ x ∈ domains 15, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint15 : ∀ j ∈ List.range 47, 15 ≠ j →
    ∀ x ∈ domains 15, x ∉ domains j := by
  decide +kernel
private theorem fresh16 : ∀ x ∈ domains 16, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint16 : ∀ j ∈ List.range 47, 16 ≠ j →
    ∀ x ∈ domains 16, x ∉ domains j := by
  decide +kernel
private theorem fresh17 : ∀ x ∈ domains 17, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint17 : ∀ j ∈ List.range 47, 17 ≠ j →
    ∀ x ∈ domains 17, x ∉ domains j := by
  decide +kernel
private theorem fresh18 : ∀ x ∈ domains 18, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint18 : ∀ j ∈ List.range 47, 18 ≠ j →
    ∀ x ∈ domains 18, x ∉ domains j := by
  decide +kernel
private theorem fresh19 : ∀ x ∈ domains 19, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint19 : ∀ j ∈ List.range 47, 19 ≠ j →
    ∀ x ∈ domains 19, x ∉ domains j := by
  decide +kernel
private theorem fresh20 : ∀ x ∈ domains 20, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint20 : ∀ j ∈ List.range 47, 20 ≠ j →
    ∀ x ∈ domains 20, x ∉ domains j := by
  decide +kernel
private theorem fresh21 : ∀ x ∈ domains 21, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint21 : ∀ j ∈ List.range 47, 21 ≠ j →
    ∀ x ∈ domains 21, x ∉ domains j := by
  decide +kernel
private theorem fresh22 : ∀ x ∈ domains 22, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint22 : ∀ j ∈ List.range 47, 22 ≠ j →
    ∀ x ∈ domains 22, x ∉ domains j := by
  decide +kernel
private theorem fresh23 : ∀ x ∈ domains 23, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint23 : ∀ j ∈ List.range 47, 23 ≠ j →
    ∀ x ∈ domains 23, x ∉ domains j := by
  decide +kernel
private theorem fresh24 : ∀ x ∈ domains 24, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint24 : ∀ j ∈ List.range 47, 24 ≠ j →
    ∀ x ∈ domains 24, x ∉ domains j := by
  decide +kernel
private theorem fresh25 : ∀ x ∈ domains 25, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint25 : ∀ j ∈ List.range 47, 25 ≠ j →
    ∀ x ∈ domains 25, x ∉ domains j := by
  decide +kernel
private theorem fresh26 : ∀ x ∈ domains 26, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint26 : ∀ j ∈ List.range 47, 26 ≠ j →
    ∀ x ∈ domains 26, x ∉ domains j := by
  decide +kernel
private theorem fresh27 : ∀ x ∈ domains 27, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint27 : ∀ j ∈ List.range 47, 27 ≠ j →
    ∀ x ∈ domains 27, x ∉ domains j := by
  decide +kernel
private theorem fresh28 : ∀ x ∈ domains 28, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint28 : ∀ j ∈ List.range 47, 28 ≠ j →
    ∀ x ∈ domains 28, x ∉ domains j := by
  decide +kernel
private theorem fresh29 : ∀ x ∈ domains 29, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint29 : ∀ j ∈ List.range 47, 29 ≠ j →
    ∀ x ∈ domains 29, x ∉ domains j := by
  decide +kernel
private theorem fresh30 : ∀ x ∈ domains 30, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint30 : ∀ j ∈ List.range 47, 30 ≠ j →
    ∀ x ∈ domains 30, x ∉ domains j := by
  decide +kernel
private theorem fresh31 : ∀ x ∈ domains 31, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint31 : ∀ j ∈ List.range 47, 31 ≠ j →
    ∀ x ∈ domains 31, x ∉ domains j := by
  decide +kernel
private theorem fresh32 : ∀ x ∈ domains 32, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint32 : ∀ j ∈ List.range 47, 32 ≠ j →
    ∀ x ∈ domains 32, x ∉ domains j := by
  decide +kernel
private theorem fresh33 : ∀ x ∈ domains 33, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint33 : ∀ j ∈ List.range 47, 33 ≠ j →
    ∀ x ∈ domains 33, x ∉ domains j := by
  decide +kernel
private theorem fresh34 : ∀ x ∈ domains 34, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint34 : ∀ j ∈ List.range 47, 34 ≠ j →
    ∀ x ∈ domains 34, x ∉ domains j := by
  decide +kernel
private theorem fresh35 : ∀ x ∈ domains 35, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint35 : ∀ j ∈ List.range 47, 35 ≠ j →
    ∀ x ∈ domains 35, x ∉ domains j := by
  decide +kernel
private theorem fresh36 : ∀ x ∈ domains 36, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint36 : ∀ j ∈ List.range 47, 36 ≠ j →
    ∀ x ∈ domains 36, x ∉ domains j := by
  decide +kernel
private theorem fresh37 : ∀ x ∈ domains 37, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint37 : ∀ j ∈ List.range 47, 37 ≠ j →
    ∀ x ∈ domains 37, x ∉ domains j := by
  decide +kernel
private theorem fresh38 : ∀ x ∈ domains 38, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint38 : ∀ j ∈ List.range 47, 38 ≠ j →
    ∀ x ∈ domains 38, x ∉ domains j := by
  decide +kernel
private theorem fresh39 : ∀ x ∈ domains 39, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint39 : ∀ j ∈ List.range 47, 39 ≠ j →
    ∀ x ∈ domains 39, x ∉ domains j := by
  decide +kernel
private theorem fresh40 : ∀ x ∈ domains 40, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint40 : ∀ j ∈ List.range 47, 40 ≠ j →
    ∀ x ∈ domains 40, x ∉ domains j := by
  decide +kernel
private theorem fresh41 : ∀ x ∈ domains 41, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint41 : ∀ j ∈ List.range 47, 41 ≠ j →
    ∀ x ∈ domains 41, x ∉ domains j := by
  decide +kernel
private theorem fresh42 : ∀ x ∈ domains 42, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint42 : ∀ j ∈ List.range 47, 42 ≠ j →
    ∀ x ∈ domains 42, x ∉ domains j := by
  decide +kernel
private theorem fresh43 : ∀ x ∈ domains 43, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint43 : ∀ j ∈ List.range 47, 43 ≠ j →
    ∀ x ∈ domains 43, x ∉ domains j := by
  decide +kernel
private theorem fresh44 : ∀ x ∈ domains 44, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint44 : ∀ j ∈ List.range 47, 44 ≠ j →
    ∀ x ∈ domains 44, x ∉ domains j := by
  decide +kernel
private theorem fresh45 : ∀ x ∈ domains 45, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint45 : ∀ j ∈ List.range 47, 45 ≠ j →
    ∀ x ∈ domains 45, x ∉ domains j := by
  decide +kernel
private theorem fresh46 : ∀ x ∈ domains 46, Fresh 196 maker breaker x := by
  unfold Fresh
  decide +kernel
private theorem disjoint46 : ∀ j ∈ List.range 47, 46 ≠ j →
    ∀ x ∈ domains 46, x ∉ domains j := by
  decide +kernel
theorem fresh_domains : ∀ i ∈ List.range 47, ∀ x ∈ domains i,
    Fresh 196 maker breaker x := by
  intro i hi
  have hiN : i < 47 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fresh0
  · exact fresh1
  · exact fresh2
  · exact fresh3
  · exact fresh4
  · exact fresh5
  · exact fresh6
  · exact fresh7
  · exact fresh8
  · exact fresh9
  · exact fresh10
  · exact fresh11
  · exact fresh12
  · exact fresh13
  · exact fresh14
  · exact fresh15
  · exact fresh16
  · exact fresh17
  · exact fresh18
  · exact fresh19
  · exact fresh20
  · exact fresh21
  · exact fresh22
  · exact fresh23
  · exact fresh24
  · exact fresh25
  · exact fresh26
  · exact fresh27
  · exact fresh28
  · exact fresh29
  · exact fresh30
  · exact fresh31
  · exact fresh32
  · exact fresh33
  · exact fresh34
  · exact fresh35
  · exact fresh36
  · exact fresh37
  · exact fresh38
  · exact fresh39
  · exact fresh40
  · exact fresh41
  · exact fresh42
  · exact fresh43
  · exact fresh44
  · exact fresh45
  · exact fresh46
theorem disjoint_domains : DomainsDisjoint 47 domains := by
  intro i hi
  have hiN : i < 47 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact disjoint27
  · exact disjoint28
  · exact disjoint29
  · exact disjoint30
  · exact disjoint31
  · exact disjoint32
  · exact disjoint33
  · exact disjoint34
  · exact disjoint35
  · exact disjoint36
  · exact disjoint37
  · exact disjoint38
  · exact disjoint39
  · exact disjoint40
  · exact disjoint41
  · exact disjoint42
  · exact disjoint43
  · exact disjoint44
  · exact disjoint45
  · exact disjoint46
theorem component_defenses : ∀ i ∈ List.range 47,
    ¬ BlackWins (targets i) 196 [] (outside 196 (domains i)) := by
  intro i hi
  have hiN : i < 47 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_component_not_blackWins (N := 196) (a := 0) (b := 14) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 1) (b := 56) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 2) (b := 4) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 3) (b := 17) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 5) (b := 6) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 7) (b := 8) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 9) (b := 37) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 10) (b := 20) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 11) (b := 12) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 15) (b := 16) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 18) (b := 19) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 21) (b := 22) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 23) (b := 24) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 28) (b := 45) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 29) (b := 70) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 30) (b := 31) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 32) (b := 46) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 38) (b := 39) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 42) (b := 85) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 43) (b := 44) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 57) (b := 71) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 58) (b := 72) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 84) (b := 98) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 86) (b := 100) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 99) (b := 113) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 112) (b := 126) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 114) (b := 142) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 127) (b := 128) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 140) (b := 168) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 141) (b := 155) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 151) (b := 165) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 152) (b := 166) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 153) (b := 167) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 156) (b := 170) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 157) (b := 158) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 159) (b := 160) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 161) (b := 188) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 163) (b := 177) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 171) (b := 172) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 175) (b := 176) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 178) (b := 179) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 180) (b := 191) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 181) (b := 194) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 185) (b := 186) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 189) (b := 190) (by decide) (by decide) (by decide)
  · exact pair_component_not_blackWins (N := 196) (a := 192) (b := 193) (by decide) (by decide) (by decide)
  · exact C00.defense

end Snaky.BreakerN32
