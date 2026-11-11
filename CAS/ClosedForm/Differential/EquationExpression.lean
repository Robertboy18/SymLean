/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Differential.Requirements

/-!
# Symbolic equations and their lowered residuals

`DiffExpr.Equation` is a pair of differential expressions `lhs` and `rhs`; systems are indexed
families of equations. `Equation.closedResidual` lowers the residual `lhs - rhs` for an ansatz
with `DiffExpr.lower`, which computes its derivatives symbolically without any analytic
derivative, and `Equation.ClosedResidualVanishesAt` states that the lowered residual is zero at
a point.
-/

@[expose] public section

namespace CAS

namespace DiffExpr

/-- A scalar symbolic differential equation. Systems are represented by indexed families of
equations. -/
structure Equation (n : Nat) (σ : Type*) where
  /-- The left-hand side of the differential equation. -/
  lhs : DiffExpr n σ
  /-- The right-hand side of the differential equation. -/
  rhs : DiffExpr n σ
deriving Repr

namespace Equation

/-- The residual `lhs - rhs`. -/
def residual {n : Nat} {σ : Type*} (eqn : Equation n σ) : DiffExpr n σ :=
  .sub eqn.lhs eqn.rhs

/-- Substitute an ansatz and lower the equation's residual to a closed-form expression. -/
def closedResidual {n : Nat} {σ : Type*}
    (ansatz : σ → Verified.Expr (Fin n)) (eqn : Equation n σ) : Verified.Expr (Fin n) :=
  lower ansatz eqn.residual

/-- The lowered residual vanishes at the given point. -/
def ClosedResidualVanishesAt {n : Nat} {σ : Type*}
    (ansatz : σ → Verified.Expr (Fin n)) (eqn : Equation n σ) (x : ℝ^n) : Prop :=
  (closedResidual ansatz eqn).eval x = 0

end Equation

end DiffExpr

end CAS
