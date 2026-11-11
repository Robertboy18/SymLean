/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Exact.ExpressionSideConditions
public import CAS.Polynomial.RealRoot.Interval

/-!
# Symbolic-expression bridge for polynomial root certificates

The executable root layer works on the shared sparse polynomial representation. An accepted
root-free interval for the reflection of an expression `Verified.Expr (Fin 1)` gives the
expression-level nonzero certificate `exprNonzeroCertOfPolynomialRootFree`, an
`Exact.ExprNonzeroCert`: the certificate type for the nonzero side conditions of the closed-form
pipelines (`CAS/Exact/ExpressionSideConditions.lean`). `nonzeroOn_of_rootFreeOn_eq_true` is the
corresponding automatic check. No other module calls either of them. The bridge needs only the
reflection equation `eval_eq_sparseEvalReal` of `Verified.Expr.Alg.mvPolyOf?`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum
open CAS.Domain

/-- One-dimensional Euclidean points whose coordinate lies in a rational interval. -/
def euclideanInterval (I : RationalInterval) : Set (ℝ^1) :=
  {point | point (0 : Fin 1) ∈ Icc (I.lo : ℝ) (I.hi : ℝ)}

private theorem point_eq_single (point : ℝ^1) :
    point = EuclideanSpace.single (0 : Fin 1) (point (0 : Fin 1)) := by
  ext i
  fin_cases i
  simp

/-- Reflection identifies expression evaluation with shared sparse evaluation. -/
theorem eval_eq_sparseEvalReal {expr : Verified.Expr (Fin 1)} {polynomial : Sparse.Univariate}
    (hreflect : Verified.Expr.Alg.mvPolyOf? expr = some polynomial)
    (point : ℝ^1) :
    expr.eval point =
      Sparse.evalReal polynomial (point (0 : Fin 1)) := by
  rw [Sparse.evalReal_eq_mvPolyVal, ← point_eq_single point]
  exact (Verified.Expr.Alg.mvPolyVal_eq_eval_of_mvPolyOf? point expr polynomial hreflect).symm

/--
An accepted root-free sparse-polynomial interval discharges the corresponding
symbolic expression's nonzero side condition.
-/
noncomputable def exprNonzeroCertOfPolynomialRootFree
    (expr : Verified.Expr (Fin 1)) (polynomial : Sparse.Univariate)
    (interval : RationalInterval)
    (hreflect : Verified.Expr.Alg.mvPolyOf? expr = some polynomial)
    (hvalid : rootFree polynomial interval = true) :
    Exact.ExprNonzeroCert 1 (euclideanInterval interval) :=
  ⟨expr, by
    intro point hpoint
    rw [Exact.exprFn, eval_eq_sparseEvalReal hreflect point]
    exact
      nonzeroOn_of_rootFree_eq_true polynomial interval hvalid
        (point (0 : Fin 1)) hpoint⟩

/--
Automatically check whether a one-variable symbolic polynomial is root-free
on a rational interval.

Non-polynomial expressions return `false`.
-/
def rootFreeOn (expr : Verified.Expr (Fin 1)) (I : RationalInterval) : Bool :=
  match Verified.Expr.Alg.mvPolyOf? expr with
  | none => false
  | some polynomial => rootFree polynomial I

/-- A successful automatic root-free check proves the ordinary semantic nonzero statement. -/
theorem nonzeroOn_of_rootFreeOn_eq_true
    (expr : Verified.Expr (Fin 1)) (I : RationalInterval)
    (hcheck : rootFreeOn expr I = true) :
    NonzeroOn (Exact.exprFn expr) (euclideanInterval I) := by
  unfold rootFreeOn at hcheck
  split at hcheck
  · cases hcheck
  · next polynomial hreflect =>
    exact (exprNonzeroCertOfPolynomialRootFree expr polynomial I hreflect hcheck).sound

end CAS.Polynomial.RealRoot
