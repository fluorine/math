import Snaky.E1Data

namespace Snaky.E1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row (mask : Nat) : List Nat :=
  ((List.range 9).filter fun i => (mask / 2^i) % 2 == 1).map (30 + ·)

def runs (mask : Nat) : List Nat :=
  (List.range 6).filter fun i =>
    (List.range 4).all fun j => (row mask).contains (30 + i + j)

def validRow (mask : Nat) : Bool := (runs mask).length ≤ 1

def phase (mask : Nat) : Nat :=
  match (runs mask).head? with
  | none => 0
  | some i => (i + 1) % 2

def pairsFor (p m : Nat) : List Pair :=
  match p, m with
  | 0, 0 => pairs00
  | 0, 1 => pairs01
  | 0, _ => pairs02
  | _, 0 => pairs10
  | _, 1 => pairs11
  | _, _ => pairs12

def uncoveredFor (p m : Nat) : List (List Nat) :=
  match p, m with
  | 0, 0 => uncovered00
  | 0, 1 => uncovered01
  | 0, _ => uncovered02
  | _, 0 => uncovered10
  | _, 1 => uncovered11
  | _, _ => uncovered12


def forbiddenSets : List (List Nat) :=
  [[42,52,53,63,73], [72,73,74,85], [43,53,63,73,74],
   [58,65,66,67,68,74,75], [65,66,67,68,74,75,78]]

def modePositive : Nat → List Nat
  | 0 => []
  | 1 => [73,74]
  | _ => [65,66,67,68,73,74,75]

def modeForbidden : Nat → List (List Nat)
  | 0 => [[73,74]]
  | 1 => [[65,66,67,68,74,75]]
  | _ => []

def config (mask mode : Nat) : CoreCase :=
  { positive := row mask ++ modePositive mode
    negative := ((List.range 9).map (30 + ·)).filter fun x => !(row mask).contains x
    forbidden := forbiddenSets ++ modeForbidden mode
    pairs := pairsFor (phase mask) mode }


def validMasks : List Nat := (List.range 512).filter validRow

def checkMask (mask : Nat) : Bool :=
  (List.range 3).all fun mode =>
    (uncoveredFor (phase mask) mode).all (rejected (config mask mode))

end Snaky.E1
