/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.IntervalIntegral
public import CAS.Expr.NamedVariables
public import CAS.Expr.Simplify

/-!
# Checked symbolic partial derivatives

`closedPartial v expr` is the symbolic derivative `expr.diff v` followed by the trigonometric
simplifier `trigSimplify`, which preserves evaluation (`eval_trigSimplify`). At a valid point its
value is therefore the coordinate derivative of `x ↦ expr.eval x`; `CAS.Calculus.FDeriv` proves
this as `fderiv_eval_apply_eq_sum_closedPartial`. Without any validity hypothesis, the checked
partial of a list sum evaluates to the sum of the checked partials of its terms.

Coordinate names and the conversion from presentation-level variables to semantic indices live
in `CAS.Expr.NamedVariables`; `closedPartialBy` and the notation `∂ₛ[i]` accept either form.

## Main definitions

* `closedPartial`, `closedPartialBy`: the checked partial derivative, by index or by name.

## Main results

* `eval_closedPartial_addList`: the checked partial of a list sum evaluates termwise.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Closed-form symbolic partial derivative. -/
def closedPartial {ι : Type*} [DecidableEq ι] (v : ι) (expr : Verified.Expr ι) :
    Verified.Expr ι :=
  trigSimplify (expr.diff v)

/-- The checked partial derivative of a symbolic list sum evaluates termwise. -/
@[simp] theorem eval_closedPartial_addList {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (v : ι) (xs : List (Verified.Expr ι)) :
    (closedPartial v (Verified.Expr.addList xs)).eval ρ =
      (xs.map fun expr ↦ (closedPartial v expr).eval ρ).sum := by
  cases xs with
  | nil => simp [addList, closedPartial]
  | cons hd tl =>
    simp only [addList]
    induction tl generalizing hd with
    | nil => simp
    | cons x xs ih => simpa [closedPartial, add_assoc] using ih (.add hd x)

/-- Closed-form symbolic partial derivative with respect to either an index or a named variable. -/
def closedPartialBy {ι : Type*} {ν : Type*} [DecidableEq ι] [DiffVar ν ι]
    (v : ν) (expr : Verified.Expr ι) : Verified.Expr ι :=
  closedPartial (DiffVar.index v) expr

/-- Checked symbolic partial derivative notation: `∂ₛ[i] expr`. -/
notation "∂ₛ[" i "] " e:arg => Verified.Expr.closedPartialBy i e

end Verified.Expr

end CAS
