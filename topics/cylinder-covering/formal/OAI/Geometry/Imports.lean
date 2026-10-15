module

public import OAI.Geometry.ArithmeticImports
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Affine.Simplex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.WLOG

/-! Explicit imports for the unchanged OAI geometric proof bodies.

This file replaces the upstream umbrella `import Mathlib` so that the same
proofs can be checked within the published single-process memory budget.
No declaration, hypothesis, or proof body from the source is changed.
-/
