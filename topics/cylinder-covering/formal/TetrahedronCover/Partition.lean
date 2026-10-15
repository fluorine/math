module

public import TetrahedronCover.Definitions
public import OAI.Geometry.CylinderCovering.Convexity.GeneralCapCoverage

/-! Positive finite partitions of the full closed angular interval.

The node function is extended beyond the last node only to match the
first-crossing interface in the pinned OAI source. No assertion or construction
uses that extension. In particular, `cell` contains exactly `count` cells.
-/
@[expose] public section

namespace TetrahedronCover
noncomputable section

/-- A strictly positive finite partition of `[-1,1]`, including both endpoints. -/
structure Partition where
  count : ℕ
  positive : 0 < count
  node : ℕ → ℝ
  first : node 0 = -1
  last : node count = 1
  increasing : ∀ i < count, node i < node (i + 1)

namespace Partition

theorem node_bounds (P : Partition) (i : ℕ) (hi : i ≤ P.count) :
    |P.node i| ≤ 1 :=
  OAI.CylinderCovering.GeneralCap.node_bounds P.node P.first P.last P.increasing i hi

def cell (P : Partition) (i : Fin P.count) : Cell where
  left := P.node i
  right := P.node (i + 1)
  left_ge := (abs_le.mp (P.node_bounds i i.isLt.le)).1
  right_le := (abs_le.mp (P.node_bounds (i + 1) i.isLt)).2
  strict := P.increasing i i.isLt

/-- Secant slope data, with the same harmless extension as the node function. -/
def slope (P : Partition) (i : ℕ) : ℝ := (1 + P.node i * P.node (i + 1)) / 2

def mid (P : Partition) (i : ℕ) : ℝ := (P.node i + P.node (i + 1)) / 2

def boundary (P : Partition) (i : ℕ) : ℝ := D (P.node i)

@[simp] theorem cell_slope (P : Partition) (i : Fin P.count) :
    (P.cell i).slope = P.slope i := rfl

@[simp] theorem cell_mid (P : Partition) (i : Fin P.count) :
    (P.cell i).mid = P.mid i := rfl

theorem boundary_first (P : Partition) : P.boundary 0 = 0 := by
  simp [boundary, D, P.first]

theorem boundary_last (P : Partition) : P.boundary P.count = 0 := by
  simp [boundary, D, P.last]

theorem shared_left (P : Partition) (i : ℕ) :
    P.slope i - P.node i * P.mid i = P.boundary i := by
  dsimp [slope, mid, boundary, D]
  ring

theorem shared_right (P : Partition) (i : ℕ) :
    P.slope i - P.node (i + 1) * P.mid i = P.boundary (i + 1) := by
  dsimp [slope, mid, boundary, D]
  ring

/-- First crossing works on the boundary too, and does not divide by a radius.
The conclusion therefore includes a zero selected radius without an exception. -/
theorem angular_selection (P : Partition) {r z ell : ℝ} (hz : |z| ≤ r) :
    ∃ i : Fin P.count, ∃ q : ℝ, (P.cell i).Mem q ∧
      0 ≤ r - ell * (P.cell i).mid ∧
      z = (r - ell * (P.cell i).mid) * q + ell * (P.cell i).slope := by
  obtain ⟨i, hi, q, hq, hr, hz'⟩ :=
    OAI.CylinderCovering.GeneralCap.angular_selection P.positive
      P.node P.slope P.mid P.boundary P.first P.last
      P.boundary_first P.boundary_last P.increasing
      (fun i _ => P.shared_left i) (fun i _ => P.shared_right i) hz
  exact ⟨⟨i, hi⟩, q, hq, hr, hz'⟩

end Partition

/-- The equally spaced partition, with no divisibility or parity restriction. -/
abbrev uniformPartition (N : ℕ) (hN : 0 < N) : Partition where
  count := N
  positive := hN
  node := fun i => -1 + (i : ℝ) * (2 / (N : ℝ))
  first := by simp
  last := by
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
    field_simp
    nlinarith
  increasing := by
    intro i _
    have hstep : (0 : ℝ) < 2 / (N : ℝ) :=
      div_pos (by norm_num) (Nat.cast_pos.mpr hN)
    push_cast
    nlinarith only [hstep]

@[simp] theorem uniformPartition_count (N : ℕ) (hN : 0 < N) :
    (uniformPartition N hN).count = N := rfl

theorem uniformPartition_width (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((uniformPartition N hN).cell i).width = 2 / (N : ℝ) := by
  dsimp [uniformPartition, Partition.cell, Cell.width]
  push_cast
  ring

theorem uniformPartition_left (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((uniformPartition N hN).cell i).left = -1 + (i : ℕ) * (2 / (N : ℝ)) := rfl

theorem uniformPartition_right (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((uniformPartition N hN).cell i).right = -1 + ((i : ℕ) + 1) * (2 / (N : ℝ)) := by
  simp [uniformPartition, Partition.cell]

end
end TetrahedronCover
