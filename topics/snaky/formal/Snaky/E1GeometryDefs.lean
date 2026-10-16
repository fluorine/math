import Snaky.E1Data
import Snaky.Geometry10Data

namespace Snaky.E1

def eligible (F : List Nat) : Bool :=
  F.all fun x => decide (x / 10 < 9 ∧ x % 10 < 9) &&
    !(x == 44 || x == 55)

/-- Structural insertion sort keeps the six-cell checks kernel reducible. -/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNat xs)

def traceOf (F : List Nat) : List Nat :=
  sortNat (F.filter fun x => !(x == 83 || x == 84))


end Snaky.E1
