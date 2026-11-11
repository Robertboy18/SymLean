/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.MatrixVerification.Expression

/-!
# Exact rational approximate-inverse certificate for a 2x2 matrix

If `B` is any matrix with `‖I - B A‖ < 1` in an operator norm, then `B A` is invertible by the
Neumann series, and hence so is `A`. An approximate-inverse certificate records `A`, a proposed
inverse `B`, and a bound on the residual `I - B A`; checking it is exact rational arithmetic,
and the conclusion is an `IsUnit` proof for `A`.

The smallest nontrivial case: the target is `diag(2, 3)` and the
proposed inverse `diag(1/2, 1/4)` is deliberately inexact: the residual is `diag(0, 1/4)`, with
Euclidean operator norm exactly `1/4`. Two certificate routes, the operator-norm
residual bound and entrywise bounds with absolute row sums, both prove invertibility of the
target. The second half repeats the computation with the matrices given as closed symbolic
expressions, so the residual entries are generated and enclosed by the certified
rational-interval evaluator instead of being written by hand.

## Main results

* `candidate_isCertified`, `target_isUnit`: the operator-norm certificate and the resulting
  invertibility proof.
* `entryBounds_isCertified`, `target_isUnit_from_entryBounds`: the entrywise route.
* `target_bijective`: bijectivity of the induced operator on `ℝ^2`.
* `Automatic.expressionData_certify`, `Automatic.target_isUnit_automatic`: the same conclusion
  from automatically compiled symbolic residual intervals.
-/

@[expose] public section

namespace CAS.Examples.Numerics.MatrixVerification

open CAS.Continuum.MatrixVerification
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A diagonal real matrix with exact rational entries. -/
def target : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 0; 0, 3]

/-- An exact-rational approximation to the inverse of `target`. -/
def approximateInverse : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, 0; 0, 1 / 4]

/-- Proof-free 2x2 approximate-inverse data with residual bound `1 / 4`. -/
def candidate : ApproximateInverseCandidate (Fin 2) ℝ where
  matrix := target
  proposedInverse := approximateInverse
  residualBound := 1 / 4

/-- The proposal is not an exact inverse, so the example needs the residual bound. -/
theorem proposed_product_ne_one : approximateInverse * target ≠ 1 := by
  intro h
  have := congrFun (congrFun h 1) 1
  norm_num [approximateInverse, target, Matrix.mul_apply] at this

/-- The exact left residual is the diagonal matrix `diag(0, 1 / 4)`. -/
theorem candidate_leftResidual :
    candidate.leftResidual = Matrix.diagonal ![0, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [candidate, ApproximateInverseCandidate.leftResidual,
      approximateInverse, target, Matrix.mul_apply]

/-- The exact-rational proposal satisfies the semantic residual certificate. -/
theorem candidate_isCertified : candidate.IsCertified := by
  constructor
  · rw [candidate_leftResidual, Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg (by norm_num [candidate])]
    intro i
    fin_cases i <;> norm_num [candidate]
  · norm_num [candidate]

/-- Exact entrywise bounds for the same nonzero residual. -/
def entryBounds : ResidualEntryBounds (Fin 2) :=
  !![0, 0; 0, 1 / 4]

/-- The entry bounds certify every residual entry and both absolute row sums. -/
theorem entryBounds_isCertified : entryBounds.IsCertified candidate := by
  refine ⟨?_, ?_, by norm_num [candidate]⟩
  · intro i j
    rw [candidate_leftResidual]
    fin_cases i <;> fin_cases j <;>
      norm_num [entryBounds, Matrix.diagonal]
  · intro i
    fin_cases i <;> norm_num [entryBounds, candidate]

/-- The non-exact approximate inverse certifies that `target` is invertible. -/
theorem target_isUnit : IsUnit target :=
  candidate.matrix_isUnit candidate_isCertified

/-- Entrywise row-sum checking independently certifies that `target` is invertible. -/
theorem target_isUnit_from_entryBounds : IsUnit target :=
  entryBounds.matrix_isUnit candidate entryBounds_isCertified

/-- The corresponding operator on `ℝ^2` is bijective. -/
theorem target_bijective :
    Function.Bijective
      ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) target) :=
  candidate.toEuclideanCLM_bijective candidate_isCertified

end

/-! ## Automatic symbolic residual compilation -/

namespace Automatic

open CAS.Continuum
open CAS.Continuum.MatrixVerification.Expression
open CAS.Verified

/-- Environment for closed symbolic expressions with no variables. -/
def closedEnvironment (_point : Unit) (i : Fin 0) : ℝ :=
  Fin.elim0 i

/-- Certified evaluator context for closed symbolic expressions. -/
def closedContext :
    ExprIntervalContext RationalInterval Set.univ closedEnvironment where
  eval := RationalInterval.evalPolynomial Fin.elim0
  sound := by
    intro expr result hresult _point _hpoint
    exact RationalInterval.evalPolynomial_sound Fin.elim0 Fin.elim0
      (fun i ↦ Fin.elim0 i) expr result hresult

/-- Symbolic target matrix used by the automatic expression checker. -/
def targetExpression : Matrix (Fin 2) (Fin 2) (Expr (Fin 0)) :=
  fun i j ↦
    if i = j then
      if i = 0 then .nat 2 else .nat 3
    else
      .nat 0

/-- Symbolic inexact inverse proposal. -/
def inverseExpression : Matrix (Fin 2) (Fin 2) (Expr (Fin 0)) :=
  fun i j ↦
    if i = j then
      if i = 0 then .rat 1 2 else .rat 1 4
    else
      .nat 0

/-- Symbolic input whose residual entries will be generated and enclosed automatically. -/
def expressionData : ApproximateInverseData 2 (Fin 0) where
  matrix := targetExpression
  proposedInverse := inverseExpression

/-- Exact output expected from automatic residual interval evaluation. -/
def residualIntervals : ResidualIntervals 2 :=
  !![RationalInterval.const 0, RationalInterval.const 0;
     RationalInterval.const 0, RationalInterval.const (1 / 4)]

/-- The certified evaluator computes the expected enclosure for every generated residual entry. -/
theorem expressionData_compileResidual :
    expressionData.compileResidual? closedContext = some residualIntervals := by
  have heval :
      evalMatrix? closedContext expressionData.leftResidual =
        some residualIntervals := by
    apply evalMatrix?_eq_some_of_apply
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [expressionData, ApproximateInverseData.leftResidual,
        Expression.leftResidual, Expression.mul, Expression.one, closedContext,
        targetExpression, inverseExpression, RationalInterval.evalPolynomial,
        RationalInterval.verifiedExprOps, IntervalExprOps.eval, IntervalExprOps.sub?, Expr.addList,
        Expr.add_eq_constructor, Expr.mul_eq_constructor, Expr.sub_eq_constructor,
        residualIntervals, List.finRange]
  unfold ApproximateInverseData.compileResidual?
  rw [heval]

/-- The checker computes all residual entries and verifies the strict row-sum threshold. -/
theorem expressionData_certify :
    expressionData.certify? closedContext = some residualIntervals := by
  unfold ApproximateInverseData.certify?
  rw [expressionData_compileResidual]
  change (if residualIntervals.residualBound < 1 then some residualIntervals else none) =
    some residualIntervals
  rw [ite_eq_left (by
    norm_num [residualIntervals, ResidualIntervals.residualBound,
      ResidualIntervals.rowSum, RationalInterval.absMax_eq_max,
      List.finRange])]

/-- Automatic symbolic interval compilation proves the target matrix invertible. -/
theorem targetExpression_isUnit :
    IsUnit (evalMatrix (closedEnvironment ()) targetExpression) := by
  exact expressionData.matrix_isUnitAt closedContext residualIntervals
    expressionData_certify () (by simp)

/-- Evaluating the closed symbolic target recovers the original real matrix. -/
theorem evalMatrix_targetExpression :
    evalMatrix (closedEnvironment ()) targetExpression = target := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evalMatrix, closedEnvironment, targetExpression, target]

/-- The automatic expression checker proves the original target matrix invertible. -/
theorem target_isUnit_automatic : IsUnit target := by
  rw [← evalMatrix_targetExpression]
  exact targetExpression_isUnit

end Automatic

end CAS.Examples.Numerics.MatrixVerification
