/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The preconditioned fixed-point map of a Krawczyk argument

For a map `F` on `EuclideanSpace ℝ n` and a proposed inverse `B`, `fixedPointMap F B` is
`x ↦ x - B F(x)`. When `F` has Jacobian `J` at `x`, the derivative of this map at `x` is
`residualOperator B J = I - B J` (`hasFDerivAt_fixedPointMap`), and every zero of `F` is a fixed
point (`isFixedPt_fixedPointMap_of_eq_zero`). `B` is numerical data and is not assumed
invertible. `Krawczyk.Certificate` shows that a bound on the residual makes the map a contraction
and that `B` is then invertible.
-/

@[expose] public section

namespace CAS.Continuum.Krawczyk

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a square matrix to the corresponding real Euclidean space. -/
abbrev matrixOperator (matrix : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) matrix

/--
The preconditioned fixed-point map `x ↦ x - B F(x)` associated with a proposed inverse `B`.
-/
def fixedPointMap (function : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (approximateInverse : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  x - matrixOperator approximateInverse (function x)

/-- Matrix residual `I - B J` associated with an approximate inverse and a Jacobian. -/
def residualMatrix (approximateInverse jacobian : Matrix n n ℝ) : Matrix n n ℝ :=
  1 - approximateInverse * jacobian

/-- The derivative predicted for the preconditioned fixed-point map. -/
def residualOperator (approximateInverse jacobian : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  1 - (matrixOperator approximateInverse).comp (matrixOperator jacobian)

/-- The operator residual is the Euclidean action of the matrix residual. -/
theorem residualOperator_eq_matrixOperator
    (approximateInverse jacobian : Matrix n n ℝ) :
    residualOperator approximateInverse jacobian =
      matrixOperator (residualMatrix approximateInverse jacobian) := by
  simp only [residualOperator, residualMatrix, matrixOperator, map_sub, map_one, map_mul]
  congr 1

/-- If `F` has Jacobian `J` at `x`, then `x ↦ x - B F(x)` has derivative `I - B J` at `x`. -/
theorem hasFDerivAt_fixedPointMap
    {function : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {approximateInverse jacobian : Matrix n n ℝ}
    {x : EuclideanSpace ℝ n}
    (hjacobian : HasFDerivAt function (matrixOperator jacobian) x) :
    HasFDerivAt (fixedPointMap function approximateInverse)
      (residualOperator approximateInverse jacobian) x :=
  (hasFDerivAt_id x).sub ((matrixOperator approximateInverse).hasFDerivAt.comp x hjacobian)

/-- Every zero of the system is a fixed point of its preconditioned map. -/
theorem isFixedPt_fixedPointMap_of_eq_zero
    {function : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {approximateInverse : Matrix n n ℝ}
    {x : EuclideanSpace ℝ n}
    (hzero : function x = 0) :
    Function.IsFixedPt (fixedPointMap function approximateInverse) x := by
  simp [Function.IsFixedPt, fixedPointMap, hzero]

end

end CAS.Continuum.Krawczyk
