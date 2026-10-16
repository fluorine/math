import Snaky.Geometry14Data

namespace Snaky.Geometry14

def group0 : List (List Nat) := part00 ++ part01 ++ part02 ++ part03 ++ part04 ++ part05 ++ part06 ++ part07 ++ part08 ++ part09 ++ part10 ++ part11 ++ part12 ++ part13
def group1 : List (List Nat) := part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24 ++ part25 ++ part26 ++ part27
def group2 : List (List Nat) := part28 ++ part29 ++ part30 ++ part31 ++ part32 ++ part33 ++ part34 ++ part35 ++ part36 ++ part37 ++ part38 ++ part39 ++ part40 ++ part41
def group3 : List (List Nat) := part42 ++ part43 ++ part44 ++ part45 ++ part46 ++ part47 ++ part48 ++ part49 ++ part50 ++ part51 ++ part52 ++ part53 ++ part54 ++ part55
def group4 : List (List Nat) := part56 ++ part57 ++ part58 ++ part59 ++ part60 ++ part61 ++ part62 ++ part63 ++ part64 ++ part65 ++ part66 ++ part67 ++ part68 ++ part69
def group5 : List (List Nat) := part70 ++ part71 ++ part72 ++ part73 ++ part74 ++ part75 ++ part76 ++ part77 ++ part78 ++ part79 ++ part80 ++ part81 ++ part82 ++ part83
def group6 : List (List Nat) := part84 ++ part85 ++ part86 ++ part87 ++ part88 ++ part89 ++ part90 ++ part91 ++ part92 ++ part93 ++ part94 ++ part95 ++ part96 ++ part97
def group7 : List (List Nat) := part98 ++ part99 ++ part100 ++ part101 ++ part102 ++ part103 ++ part104 ++ part105 ++ part106 ++ part107 ++ part108 ++ part109 ++ part110 ++ part111

theorem targets_eq_groups : targets = group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 := by
  simp only [targets, group0, group1, group2, group3, group4, group5, group6, group7, List.append_assoc]

end Snaky.Geometry14
