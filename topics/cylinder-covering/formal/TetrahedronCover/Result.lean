module

public import TetrahedronCover.Geometry
public import TetrahedronCover.Benchmark

/-! The benchmark as a theorem about the actual closed Euclidean tetrahedron. -/
@[expose] public section
namespace TetrahedronCover
noncomputable section
open OAI.TriangularCovering

/-- The explicit 20,000 labeled physical cylinders, each with a compact,
nondegenerate triangular base in the plane perpendicular to its unit axis. -/
def benchmarkFamily : Fin 20000 → TriCylinder :=
  finiteFamily benchmarkPartition (1/10) (by norm_num) (by norm_num)

theorem benchmarkFamily_cost : totalArea benchmarkFamily / A_min = benchmarkCost := by
  exact finiteFamily_total benchmarkPartition (1/10) (by norm_num) (by norm_num)

/-- Complete closed-body coverage together with the exact rational area interval. -/
theorem tetrahedron_20000 :
    Covers benchmarkFamily ∧
    (499921585997001674 / 1000000000000000000 : ℝ) ≤ totalArea benchmarkFamily / A_min ∧
    totalArea benchmarkFamily / A_min ≤ (499921585997001774 / 1000000000000000000 : ℝ) ∧
    totalArea benchmarkFamily / A_min < (499922/1000000 : ℝ) := by
  refine ⟨finiteFamily_covers benchmarkPartition (by norm_num) (by norm_num), ?_⟩
  rw [benchmarkFamily_cost]
  exact ⟨benchmark_interval.1, benchmark_interval.2, benchmark_strict⟩

/-- An existential statement makes the size, geometry, and strict half-area saving explicit. -/
theorem exists_triangular_cover_below_half :
    ∃ c : Fin 20000 → TriCylinder, Covers c ∧ totalArea c < A_min/2 := by
  refine ⟨benchmarkFamily, tetrahedron_20000.1, ?_⟩
  have hpos : 0 < A_min := by rw [projection_minimum]; exact H_pos
  have hhalf : totalArea benchmarkFamily / A_min < 1/2 :=
    lt_trans tetrahedron_20000.2.2.2 (by norm_num)
  have h := (div_lt_iff₀ hpos).mp hhalf
  linarith only [h]

end
end TetrahedronCover
