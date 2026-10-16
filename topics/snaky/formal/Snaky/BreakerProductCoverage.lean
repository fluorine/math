import Snaky.BreakerProduct

namespace Snaky.Breaker

theorem productCovers_append {P Q : List (List Nat)} {W : List Nat}
    {k : Nat} {targets : Nat → List (List Nat)}
    (hp : ProductCovers P W k targets) (hq : ProductCovers Q W k targets) :
    ProductCovers (P ++ Q) W k targets := by
  intro e he hclear
  rcases List.mem_append.mp he with he | he
  · exact hp e he hclear
  · exact hq e he hclear

end Snaky.Breaker
