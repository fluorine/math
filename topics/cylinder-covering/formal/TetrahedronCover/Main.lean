module

public import TetrahedronCover.Result
public import TetrahedronCover.Schedule
public import TetrahedronCover.Nonuniform

/-! Public quantitative statements for the actual geometric cylinders.
No area estimate, coverage statement, or discretization estimate is assumed. -/
@[expose] public section
namespace TetrahedronCover
noncomputable section
open OAI.TriangularCovering

/-- The physical finite family on the equally spaced N-cell mesh. -/
def uniformFamily (N : ℕ) (hN : 0 < N) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    Fin (2*N) → TriCylinder := finiteFamily (uniformPartition N hN) e he he1

theorem uniformFamily_cost (N : ℕ) (hN : 0 < N) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    totalArea (uniformFamily N hN e he he1)/A_min =
      partitionCost (uniformPartition N hN) e :=
  finiteFamily_total (uniformPartition N hN) e he he1

/-- Universal coverage and exact maximum axis tangent on every positive uniform mesh. -/
theorem effective_triangular_covers (N : ℕ) (hN : 0 < N) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) :
    Covers (uniformFamily N hN e he he1) ∧
    IsGreatest (Set.range (familyAxisTangent (uniformPartition N hN) e he he1))
      (Real.sqrt 3*e*(1-1/(N : ℝ))) :=
  ⟨finiteFamily_covers (uniformPartition N hN) he he1,
    uniform_maximum_axisTangent N hN e he he1⟩

/-- The full finite-to-continuum estimate for actual Euclidean base areas. -/
theorem geometric_uniform_error (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he : 0 < e) (he1 : e ≤ 1/10) :
    |totalArea (uniformFamily N hN e he (by linarith))/A_min-J e| ≤ 2*e/(N : ℝ) := by
  rw [uniformFamily_cost]
  exact uniform_error N hN he.le he1

/-- The arbitrary-partition maximum-mesh estimate concerns the same physical family. -/
theorem geometric_nonuniform_error (P : Partition) {e : ℝ}
    (he : 0 < e) (he1 : e ≤ 1/10) :
    |totalArea (finiteFamily P e he (by linarith))/A_min-J e| ≤ e*P.mesh := by
  rw [finiteFamily_total]
  exact nonuniform_mesh_error P he.le he1

/-- The effective linear-in-inverse-tilt cell count produces the stated saving. -/
theorem geometric_effective_count (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he : 0 < e) (he1 : e ≤ 1/10) (hcount : ⌈480/e⌉₊ ≤ N) :
    Covers (uniformFamily N hN e he (by linarith)) ∧
    totalArea (uniformFamily N hN e he (by linarith))/A_min ≤ 1/2-e^2/240 := by
  constructor
  · exact finiteFamily_covers (uniformPartition N hN) he (by linarith)
  · rw [uniformFamily_cost]
    exact effective_count he he1 N hN hcount

/-- Explicit cubic and quartic terms on every count at least the prescribed schedule. -/
theorem geometric_schedule_upper (N : ℕ) (hN : 0 < N) {e : ℝ}
    (he : 0 < e) (he1 : e ≤ 1/10) (hcount : scheduleCount e ≤ N) :
    totalArea (uniformFamily N hN e he (by linarith))/A_min ≤
      1/2-e^2/60+e^3/2+(9/2 : ℝ)*e^4 := by
  rw [uniformFamily_cost]
  exact schedule_upper he he1 N hN hcount

/-- Closed-body covers with exactly twice the ceiling count and a strict area saving. -/
theorem geometric_schedule_saving {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/50) :
    ∃ c : Fin (2*scheduleCount e) → TriCylinder,
      Covers c ∧ totalArea c/A_min ≤ 1/2-(73/15000 : ℝ)*e^2 ∧
      totalArea c < A_min/2 := by
  let c := uniformFamily (scheduleCount e) (scheduleCount_pos he) e he (by linarith)
  refine ⟨c, finiteFamily_covers _ he (by linarith), ?_⟩
  have hc : totalArea c/A_min =
      partitionCost (uniformPartition (scheduleCount e) (scheduleCount_pos he)) e :=
    uniformFamily_cost _ _ _ _ _
  obtain ⟨hcost, hstrict⟩ := schedule_saving he he1 (scheduleCount e) (scheduleCount_pos he) (le_refl _)
  have hpos : 0 < A_min := by rw [projection_minimum]; exact H_pos
  constructor
  · rwa [hc]
  · rw [← hc] at hstrict
    have h := (div_lt_iff₀ hpos).mp hstrict
    linarith only [h]

/-- Quantitative actual asymptotic, with explicit uniform remainder constant and range. -/
theorem geometric_schedule_asymptotic {e : ℝ} (he : 0 < e) (he1 : e ≤ 1/10) :
    |totalArea (uniformFamily (scheduleCount e) (scheduleCount_pos he) e he (by linarith))/A_min-
      (1/2-e^2/60+e^3/2)| ≤ (9/2 : ℝ)*e^4 := by
  rw [uniformFamily_cost]
  exact schedule_asymptotic he he1

end
end TetrahedronCover
