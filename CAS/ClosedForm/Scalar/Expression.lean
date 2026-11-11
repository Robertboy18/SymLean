/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Differential.EquationExpression
public import CAS.ClosedForm.Expression.Rational.Zero

/-!
# Scalar symbolic residual construction and checking

A scalar equation has one unknown field, `Scalar.u`. `Scalar.residual` substitutes a candidate
for it and lowers the residual `lhs - rhs` of the equation with `DiffExpr.lower`, and
`Scalar.check` runs the zero test `Alg.zeroCheck` on the result.
`CheckedResidual.residual_eval_eq_zero_of_normalized_eq_zero` turns a zero normal form into a
residual that vanishes wherever the emitted denominators are nonzero. The conditions under which
the lowered derivatives are the true derivatives form a separate obligation,
`CheckedResidual.analyticRequirements`.
-/

@[expose] public section

namespace CAS

namespace Scalar

/-- The single unknown field used by scalar ODE/PDE builders. -/
abbrev Unknown : Type := PUnit

/-- The scalar unknown field, traditionally written `u`. -/
def u {n : Nat} : DiffExpr n Unknown :=
  .unknown PUnit.unit

/-- Build an ansatz assignment for the single unknown field. -/
def ansatz {n : Nat} (candidate : Verified.Expr (Fin n)) : Unknown → Verified.Expr (Fin n) :=
  fun _ ↦ candidate

/-- The scalar ansatz assigns the candidate to the unique unknown. -/
@[simp] theorem ansatz_apply {n : Nat} (candidate : Verified.Expr (Fin n)) (u : Unknown) :
    ansatz candidate u = candidate :=
  rfl

/-- Build a semantic ansatz assignment for an arbitrary Lean-function candidate. -/
def semanticAnsatz {n : Nat} (candidate : ℝ^n → ℝ) :
    Unknown → ℝ^n → ℝ :=
  fun _ ↦ candidate

/-- The semantic scalar ansatz assigns the candidate function to the unique unknown. -/
@[simp] theorem semanticAnsatz_apply {n : Nat}
    (candidate : ℝ^n → ℝ) (u : Unknown) :
    semanticAnsatz candidate u = candidate :=
  rfl

/-- Closed-form residual of a scalar equation after substituting a candidate expression. -/
def residual {n : Nat} (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  DiffExpr.Equation.closedResidual (ansatz candidate) eqn

/-- Run the checked scalar symbolic pipeline on an equation and candidate ansatz. -/
def check {n : Nat} (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n)) :
    Verified.Expr.Alg.NormResult (Fin n) :=
  Verified.Expr.Alg.zeroCheck (residual eqn candidate)

namespace CheckedResidual

/- The `Scalar.CheckedResidual` namespace holds the theorems about scalar checks. They keep two
kinds of obligation apart:

* the algebraic normalizer's denominator obligations;
* the analytic derivative-domain obligations coming from `DiffExpr` nodes. -/
/-- Finite analytic requirements for the underlying differential residual.

This is separate from `Verified.Expr.Alg.SideHolds`: the
normalizer tracks algebraic denominator obligations for the compiled residual, while
`analyticRequirements` tracks domains needed to interpret derivatives in the
original differential syntax. -/
def analyticRequirements {n : Nat} (eqn : DiffExpr.Equation n Unknown)
    (candidate : Verified.Expr (Fin n)) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  DiffExpr.analyticRequirements (ansatz candidate) eqn.residual

/-- The extracted requirements imply the recursive condition used by analytic evaluation. -/
theorem analyticSideCondition_of_requirements {n : Nat}
    (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n))
    (x : ℝ^n)
    (h :
      (analyticRequirements eqn candidate).Holds x) :
    DiffExpr.AnalyticSideCondition (ansatz candidate) x eqn.residual :=
  DiffExpr.analyticSideCondition_of_requirements (ansatz candidate) x eqn.residual h

/-
`residual_eval_eq_zero_of_normalized_eq_zero` turns a zero normal form and the normalizer's
`Verified.Expr.Alg.SideHolds` obligations into a zero residual.
-/

/-- If the normalized residual is literally `0`, then the scalar residual
evaluates to `0` wherever the emitted denominator side conditions hold. -/
theorem residual_eval_eq_zero_of_normalized_eq_zero {n : Nat}
    (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n))
    (x : ℝ^n)
    (hside :
      Verified.Expr.Alg.SideHolds x (check eqn candidate).nonzero)
    (hzero : (check eqn candidate).expr = 0) :
    (residual eqn candidate).eval x = 0 :=
  Verified.Expr.Alg.ZeroCheck.eval_eq_zero_of_expr_eq_zero (fun i : Fin n ↦ x i)
    (residual eqn candidate) hside hzero

end CheckedResidual

end Scalar

end CAS
