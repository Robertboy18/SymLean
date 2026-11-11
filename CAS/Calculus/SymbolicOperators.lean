/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Partial
public import CAS.ClosedForm.Expression.FiniteSeries

/-!
# Executable differential operators on checked expressions

The symbolic gradient `closedGradient` (notation `∇ₛ`), Laplacian `closedLaplacian`
(notation `Δₛ`), divergence `closedDivergence`, and curls `closedCurl2`, `closedCurl3` of
checked expressions, with list forms `closedGradientList` and `closedCurl3List`. They build
expression trees from `closedPartial`, `Verified.Expr.diff` and the simplifiers `simplify` and
`trigSimplify`, which preserve evaluation (`eval_simplify`, `eval_trigSimplify`). The definitions
carry no analytic statement of their own; `CAS.Calculus.Gradient` proves that `closedGradient`
evaluates to the gradient at a valid point (`closedGradient_eval_eq_gradient`).
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Closed-form symbolic gradient. -/
def closedGradient {n : Nat} (expr : Verified.Expr (Fin n)) : Fin n → Verified.Expr (Fin n) :=
  fun i ↦ closedPartial i expr

/-- Executable list form of the symbolic gradient in any finite dimension. -/
def closedGradientList {n : Nat} (expr : Verified.Expr (Fin n)) : List (Verified.Expr (Fin n)) :=
  (List.finRange n).map fun i ↦ closedPartial i expr

/-- Dimension-parametric symbolic gradient notation. -/
notation "∇ₛ " e:arg => Verified.Expr.closedGradient e

/-- Closed-form symbolic Laplacian. -/
def closedLaplacian {n : Nat} (expr : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  trigSimplify (sumFin fun i : Fin n ↦ trigSimplify ((expr.diff i).diff i))

/-- Dimension-parametric symbolic Laplacian notation. -/
notation "Δₛ " e:arg => Verified.Expr.closedLaplacian e

/-- Closed-form symbolic divergence of a vector field `F : ℝ^n → ℝ^n`. -/
def closedDivergence {n : Nat} (field : Fin n → Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  simplify (sumFin fun i : Fin n ↦ closedPartial i (field i))

/-- Two-dimensional scalar curl `∂ₓ F_y - ∂ᵧ F_x`. -/
def closedCurl2 (field : Fin 2 → Verified.Expr (Fin 2)) : Verified.Expr (Fin 2) :=
  simplify
    (closedPartial (0 : Fin 2) (field 1) -
      closedPartial (1 : Fin 2) (field 0))

/-- Three-dimensional vector curl. -/
def closedCurl3 (field : Fin 3 → Verified.Expr (Fin 3)) : Fin 3 → Verified.Expr (Fin 3)
  | ⟨0, _⟩ => simplify (closedPartial (1 : Fin 3) (field 2) - closedPartial (2 : Fin 3) (field 1))
  | ⟨1, _⟩ => simplify (closedPartial (2 : Fin 3) (field 0) - closedPartial (0 : Fin 3) (field 2))
  | ⟨2, _⟩ => simplify (closedPartial (0 : Fin 3) (field 1) - closedPartial (1 : Fin 3) (field 0))

/-- Executable list form of the three-dimensional symbolic curl. -/
def closedCurl3List (field : Fin 3 → Verified.Expr (Fin 3)) : List (Verified.Expr (Fin 3)) :=
  (List.finRange 3).map fun i ↦ closedCurl3 field i

end Verified.Expr

end CAS
