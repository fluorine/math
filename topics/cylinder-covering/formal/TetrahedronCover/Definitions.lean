module
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Explicit data of the quartic/secant tetrahedron construction.
All coordinates and costs refer to the physical Euclidean geometry in the
pinned OAI modules; these definitions introduce no axioms. -/
namespace TetrahedronCover
noncomputable section

def G (q : ℝ) : ℝ := (1 + q^2) / 2
def D (q : ℝ) : ℝ := (1 - q^2) / 2
def h (q : ℝ) : ℝ := q^2 * G q
def D₀ (q : ℝ) : ℝ := (G q)^2 + 2*q^2
def C (e q : ℝ) : ℝ := 1 + e^2 * h q + (9/16 : ℝ)*e^4
def Mstar (e : ℝ) : ℝ := 1 + e^2 + (9/16 : ℝ)*e^4
def K₀ (e : ℝ) : ℝ := Mstar e * (e + e^2/2) + 2*e^2

structure Cell where
  left : ℝ
  right : ℝ
  left_ge : -1 ≤ left
  right_le : right ≤ 1
  strict : left < right

namespace Cell

def width (I : Cell) : ℝ := I.right - I.left
def half (I : Cell) : ℝ := I.width / 2
def mid (I : Cell) : ℝ := (I.left + I.right) / 2
def slope (I : Cell) : ℝ := (1 + I.left*I.right) / 2
def boundary (I : Cell) (q : ℝ) : ℝ := I.slope - q*I.mid
def Mem (I : Cell) (q : ℝ) : Prop := I.left ≤ q ∧ q ≤ I.right

def padding (I : Cell) (e : ℝ) : ℝ :=
  (K₀ e * I.half + (Mstar e * e^2/2)*I.half^2) / (1-e)
def cap (I : Cell) (e : ℝ) : ℝ :=
  max (C e I.left) (C e I.right) + I.padding e

def term (I : Cell) (e : ℝ) : ℝ :=
  I.width * (I.cap e)^2 / (4 * Real.sqrt (1+e^2*(I.slope^2+2*I.mid^2)))
end Cell

end
end TetrahedronCover
