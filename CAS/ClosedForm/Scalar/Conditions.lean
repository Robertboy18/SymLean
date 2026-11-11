/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Scalar.Expression
public import CAS.Expr.Substitution

/-!
# Domains and point conditions

`DomainCondition` describes the region where a closed-form candidate is asserted to solve an
equation, as a Boolean combination of sign conditions on expressions, interpreted at a point by
`DomainCondition.HoldsAt`. It is separate from `Verified.Expr.ValidAt`, the validity condition
of the derivative rules. `PointCondition` is an equality checked at one explicit point, such as
ODE initial data: `PointCondition.residual` lowers `lhs - rhs` for the candidate and substitutes
the point, which leaves an expression without variables.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Scalar

/-- Symbolic pointwise domain restrictions for closed-form solution certificates.

These are separate from `Expr.ValidAt`.  `ValidAt` records analytic side conditions
needed by derivative rules; `DomainCondition` records the region on which a PDE/ODE solution is
being claimed, such as `x > 0`, `r ≠ 0`, or a union of branch domains. -/
inductive DomainCondition (n : Nat) where
  | all : DomainCondition n
  | zero : Verified.Expr (Fin n) → DomainCondition n
  | nonzero : Verified.Expr (Fin n) → DomainCondition n
  | positive : Verified.Expr (Fin n) → DomainCondition n
  | nonnegative : Verified.Expr (Fin n) → DomainCondition n
  | not : DomainCondition n → DomainCondition n
  | and : DomainCondition n → DomainCondition n → DomainCondition n
  | or : DomainCondition n → DomainCondition n → DomainCondition n
deriving Repr

namespace DomainCondition

/-- Semantic interpretation of a symbolic domain restriction at a point. -/
def HoldsAt {n : Nat} (dom : DomainCondition n) (x : ℝ^n) : Prop :=
  match dom with
  | .all => True
  | .zero expr => expr.eval x = 0
  | .nonzero expr => expr.eval x ≠ 0
  | .positive expr => 0 < expr.eval x
  | .nonnegative expr => 0 ≤ expr.eval x
  | .not a => ¬ a.HoldsAt x
  | .and a b => a.HoldsAt x ∧ b.HoldsAt x
  | .or a b => a.HoldsAt x ∨ b.HoldsAt x

/-- Symbolic inequality condition `a ≠ b`. -/
def ne {n : Nat} (a b : Verified.Expr (Fin n)) : DomainCondition n :=
  .nonzero (a - b)

/-- Symbolic strict inequality `a < b`. -/
def lt {n : Nat} (a b : Verified.Expr (Fin n)) : DomainCondition n :=
  .positive (b - a)

/-- Symbolic non-strict inequality `a ≤ b`. -/
def le {n : Nat} (a b : Verified.Expr (Fin n)) : DomainCondition n :=
  .nonnegative (b - a)

/-- Symbolic strict inequality `a > b`. -/
def gt {n : Nat} (a b : Verified.Expr (Fin n)) : DomainCondition n :=
  lt b a

/-- Symbolic non-strict inequality `a ≥ b`. -/
def ge {n : Nat} (a b : Verified.Expr (Fin n)) : DomainCondition n :=
  le b a

/-- The symbolic non-strict upper bound holds exactly when the evaluated values satisfy `≤`. -/
@[simp] theorem holdsAt_le_iff {n : Nat} (a b : Verified.Expr (Fin n)) (x : ℝ^n) :
    (le a b).HoldsAt x ↔ a.eval x ≤ b.eval x :=
  sub_nonneg

/-- The symbolic lower bound evaluates to the reversed non-strict real inequality. -/
@[simp] theorem holdsAt_ge_iff {n : Nat} (a b : Verified.Expr (Fin n)) (x : ℝ^n) :
    (ge a b).HoldsAt x ↔ b.eval x ≤ a.eval x := by
  simp [ge]

/-- Logical complement of a symbolic domain condition. -/
def compl {n : Nat} (dom : DomainCondition n) : DomainCondition n :=
  .not dom

end DomainCondition

/-- A symbolic equality checked at one explicitly supplied point.

This is useful for ODE initial values and other finite point constraints. It is not a trace
condition on the boundary of a PDE domain; boundary conditions belong in the analytic theorem
statement. -/
structure PointCondition (n : Nat) where
  /-- The closed symbolic value assigned to each coordinate of the designated point. -/
  point : Fin n → Verified.Expr (Fin 0)
  /-- The symbolic left-hand side to evaluate after candidate and point substitution. -/
  lhs : DiffExpr n Unknown
  /-- The symbolic right-hand side to evaluate after candidate and point substitution. -/
  rhs : DiffExpr n Unknown
deriving Repr

namespace PointCondition

/-- Residual obtained by substituting the candidate and then the designated point. -/
def residual {n : Nat} (condition : PointCondition n) (candidate : Verified.Expr (Fin n)) :
    Verified.Expr (Fin 0) :=
  Verified.Expr.simplify
    (Verified.Expr.mapVars condition.point
      (DiffExpr.lower (ansatz candidate) (.sub condition.lhs condition.rhs)))

end PointCondition

end Scalar

end CAS
