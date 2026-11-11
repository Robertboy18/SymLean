/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.RationalCanonical
public import CAS.Calculus.IteratedDifferentiation
public import CAS.Expr.Simplify
public import CAS.Continuum.DerivativeBounds
public import CAS.Continuum.IntervalEval.Range

/-!
# Symbolically compiled derivative bounds

Exact symbolic differentiation feeds CEGA range analysis in seven steps. The
only interval arithmetic is done by the range provider in step 5:

1. repeatedly differentiate the verified one-variable expression;
2. simplify it with the checked normalizer of the computer algebra system;
3. optionally run checked univariate rational gcd cancellation;
4. discharge every generated nonzero condition on the declared domain;
5. ask any `ExprRangeProviderOn` to enclose the checked target panel by panel;
6. transport that enclosure to Mathlib's `iteratedDerivWithin` on each panel;
7. expose the result through `IteratedDerivativeBounderOn`.

Every `RealIntervalBackend` therefore uses the same calculus theorem and the
same downstream adaptive quadrature API. Candidate generation is never trusted:
a proposed rational reduction is accepted only through a semantic equality
theorem under its explicit side conditions. Smoothness remains a separate
analytic hypothesis, as required by the Peano kernel theorems.

## Implementation notes

The bridge is `iteratedDerivWithin_univariateEval_eq_symbolicDerivative`: on a set with unique
derivatives on which `ValidIteratesOn n` holds, Mathlib's `iteratedDerivWithin` of the evaluated
expression is the value of `symbolicDerivative`. Every constructor applies it on the panel
`Icc a b` (`uniqueDiffOn_Icc`) and hands the result to `IteratedDerivativeBounderOn.ofBackend`.
The differentiation rules are therefore proved once, in that theorem, and not for each
expression; each use checks only the validity hypothesis, the side conditions of the rewrite and
the soundness of the range provider, whose intervals are proposals.
-/

@[expose] public section

namespace CAS

open Set
open Verified

noncomputable section

namespace Verified.Expr

/-- The normalized symbolic expression for the `n`-th ordinary derivative. -/
def symbolicDerivative (expr : Verified.Expr (Fin 1)) (n : ℕ) : Verified.Expr (Fin 1) :=
  Verified.Expr.simplify (expr.iteratedDiff (0 : Fin 1) n)

/-- Normalization preserves evaluation of the repeated symbolic derivative. -/
theorem symbolicDerivative_eval (expr : Verified.Expr (Fin 1)) (n : ℕ) (x : ℝ) :
    (expr.symbolicDerivative n).eval (!₂[x]) =
      (expr.iteratedDiff (0 : Fin 1) n).eval (!₂[x]) := by
  exact Verified.Expr.eval_simplify _ _

/-- The compiled derivative also denotes Mathlib's derivative within a valid domain. -/
theorem iteratedDerivWithin_univariateEval_eq_symbolicDerivative
    (expr : Verified.Expr (Fin 1)) (n : ℕ) {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hvalid : expr.ValidIteratesOn n s)
    {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n expr.univariateEval s x =
      (expr.symbolicDerivative n).eval !₂[x] := by
  rw [iteratedDerivWithin_univariateEval_eq expr n hs hvalid hx]
  exact (symbolicDerivative_eval expr n x).symm

end Verified.Expr

namespace Continuum.IteratedDerivativeBounderOn

open Verified.Expr

universe u

/--
Compile a proved rewrite of a symbolic derivative into local
`iteratedDerivWithin` bounds.

The rewrite may be a stronger normal form than the structural expression
produced directly by differentiation. Its semantic equality is an explicit
hypothesis, so rational cancellation and other rewrites that depend on side
conditions must be proved before the evaluator sees them.
-/
def ofExprWithRewrite {I : Type u} [Continuum.RealIntervalBackend I]
    (expr derivative : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hrewrite : ∀ x ∈ s,
      derivative.eval (!₂[x]) =
        (expr.symbolicDerivative n).eval (!₂[x]))
    (provider :
      Continuum.ExprRangeProviderOn (I := I) derivative
        (fun x ↦ !₂[x]) s) :
    Continuum.IteratedDerivativeBounderOn n expr.univariateEval s :=
  Continuum.IteratedDerivativeBounderOn.ofBackend
    (fun hab hsub ↦ provider.result hab hsub)
    (fun hab hsub hx ↦ by
      rw [iteratedDerivWithin_univariateEval_eq_symbolicDerivative
        expr n (uniqueDiffOn_Icc hab)
        (fun k hk x hxPanel ↦ hvalid k hk x (hsub hxPanel)) hx]
      rw [← hrewrite _ (hsub hx)]
      exact provider.sound hab hsub _ hx)

/-- The rewritten-expression bound is the absolute maximum of its backend range. -/
@[simp]
theorem ofExprWithRewrite_bound {I : Type u} [Continuum.RealIntervalBackend I]
    (expr derivative : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hrewrite : ∀ x ∈ s,
      derivative.eval (!₂[x]) =
        (expr.symbolicDerivative n).eval (!₂[x]))
    (provider :
      Continuum.ExprRangeProviderOn (I := I) derivative
        (fun x ↦ !₂[x]) s)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    (ofExprWithRewrite expr derivative n s hvalid hrewrite provider).bound hab hsub =
      max
        |Continuum.RealIntervalBackend.lo (provider.result hab hsub)|
        |Continuum.RealIntervalBackend.hi (provider.result hab hsub)| :=
  rfl

/--
Compile any checked side-aware simplification route into local derivative bounds.

The route identifies its source expression, carries the semantic
proof of its target, and exposes only the emitted side conditions to the
caller.
-/
def ofExprWithSideRoute {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (route : Verified.Expr.SideClaimRoute (Fin 1))
    (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hsource : route.lhs = expr.symbolicDerivative n)
    (hside : ∀ x ∈ s,
      Verified.Expr.Alg.SideHolds (!₂[x]) route.nonzero)
    (provider :
      Continuum.ExprRangeProviderOn (I := I) route.rhs
        (fun x ↦ !₂[x]) s) :
    Continuum.IteratedDerivativeBounderOn n expr.univariateEval s :=
  ofExprWithRewrite expr route.rhs n s hvalid
    (fun x hx ↦ by
      have hsound := route.sound (!₂[x]) (hside x hx)
      simpa [hsource] using hsound)
    provider

/-- A side-route bound is the absolute maximum of the route target's range. -/
@[simp]
theorem ofExprWithSideRoute_bound
    {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (route : Verified.Expr.SideClaimRoute (Fin 1))
    (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hsource : route.lhs = expr.symbolicDerivative n)
    (hside : ∀ x ∈ s,
      Verified.Expr.Alg.SideHolds (!₂[x]) route.nonzero)
    (provider :
      Continuum.ExprRangeProviderOn (I := I) route.rhs
        (fun x ↦ !₂[x]) s)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    (ofExprWithSideRoute expr route n s hvalid hsource hside provider).bound
        hab hsub =
      max
        |Continuum.RealIntervalBackend.lo (provider.result hab hsub)|
        |Continuum.RealIntervalBackend.hi (provider.result hab hsub)| :=
  rfl

/--
Differentiate, canonically reduce the univariate rational expression, and
compile a range provider for the canonical derivative expression into
derivative bounds.

Unsupported expressions conservatively use the identity route.  Successful
gcd cancellation is accepted only after the rational equality checker
proves the equality under the generated nonzero conditions.
-/
def ofRationalExpr {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hside : ∀ x ∈ s,
      Verified.Expr.Alg.SideHolds (!₂[x])
        (Verified.Expr.RationalCanonical.route
          (expr.symbolicDerivative n)).nonzero)
    (provider :
      Continuum.ExprRangeProviderOn (I := I)
        (Verified.Expr.RationalCanonical.route
          (expr.symbolicDerivative n)).rhs
        (fun x ↦ !₂[x]) s) :
    Continuum.IteratedDerivativeBounderOn n expr.univariateEval s :=
  ofExprWithSideRoute expr
    (Verified.Expr.RationalCanonical.route (expr.symbolicDerivative n))
    n s hvalid
    (Verified.Expr.RationalCanonical.route_lhs
      (expr.symbolicDerivative n))
    hside provider

/-- A canonically reduced rational derivative is bounded by its provider range. -/
@[simp]
theorem ofRationalExpr_bound
    {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hside : ∀ x ∈ s,
      Verified.Expr.Alg.SideHolds (!₂[x])
        (Verified.Expr.RationalCanonical.route
          (expr.symbolicDerivative n)).nonzero)
    (provider :
      Continuum.ExprRangeProviderOn (I := I)
        (Verified.Expr.RationalCanonical.route
          (expr.symbolicDerivative n)).rhs
        (fun x ↦ !₂[x]) s)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    (ofRationalExpr expr n s hvalid hside provider).bound hab hsub =
      max
        |Continuum.RealIntervalBackend.lo (provider.result hab hsub)|
        |Continuum.RealIntervalBackend.hi (provider.result hab hsub)| :=
  rfl

/--
Compile the structural normalized derivative and a backend range provider into
local `iteratedDerivWithin` bounds.
-/
def ofExpr {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (provider :
      Continuum.ExprRangeProviderOn (I := I) (expr.symbolicDerivative n)
        (fun x ↦ !₂[x]) s) :
    Continuum.IteratedDerivativeBounderOn n expr.univariateEval s :=
  Continuum.IteratedDerivativeBounderOn.ofBackend
    (fun hab hsub ↦ provider.result hab hsub)
    (fun hab hsub hx ↦ by
      rw [iteratedDerivWithin_univariateEval_eq_symbolicDerivative
        expr n (uniqueDiffOn_Icc hab)
        (fun k hk x hxPanel ↦ hvalid k hk x (hsub hxPanel)) hx]
      exact provider.sound hab hsub _ hx)

/-- The bound compiled from an expression is the absolute maximum of its backend range. -/
@[simp]
theorem ofExpr_bound {I : Type u} [Continuum.RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (provider :
      Continuum.ExprRangeProviderOn (I := I) (expr.symbolicDerivative n)
        (fun x ↦ !₂[x]) s)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    (ofExpr expr n s hvalid provider).bound hab hsub =
      max
        |Continuum.RealIntervalBackend.lo (provider.result hab hsub)|
        |Continuum.RealIntervalBackend.hi (provider.result hab hsub)| :=
  rfl

/--
Compile a derivative that normalizes to an expression independent of the
sole variable.

Only one backend input interval, enclosing zero, is required: the derivative is
evaluated once and the same range serves every panel, so the backend never has
to enclose the panel endpoints.
-/
def ofIndependentExpr {I : Type u} [Continuum.RealIntervalBackend I]
    (evaluator : Continuum.VerifiedExprIntervalEvaluator I)
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hindependent :
      Verified.Expr.containsVar (0 : Fin 1) (expr.symbolicDerivative n) = false)
    (input result : I)
    (hzero : Continuum.RealIntervalBackend.MemReal input 0)
    (hevaluated :
      evaluator.eval (fun _ : Fin 1 ↦ input) (expr.symbolicDerivative n) =
        some result) :
    Continuum.IteratedDerivativeBounderOn n expr.univariateEval s :=
  Continuum.IteratedDerivativeBounderOn.ofBackend
    (fun _hab _hsub ↦ result)
    (fun hab hsub hx ↦ by
      rw [iteratedDerivWithin_univariateEval_eq_symbolicDerivative
        expr n (uniqueDiffOn_Icc hab)
        (fun k hk x hxPanel ↦ hvalid k hk x (hsub hxPanel)) hx]
      rw [Verified.Expr.eval_eq_eval_zero_of_not_containsVar
        (expr.symbolicDerivative n) hindependent]
      exact evaluator.sound
        (fun _ : Fin 1 ↦ input)
        (!₂[(0 : ℝ)])
        (fun i ↦ by
          fin_cases i
          simpa using hzero)
        hevaluated)

/--
The bound compiled for a variable-independent derivative is the absolute
maximum of the single backend range.
-/
@[simp]
theorem ofIndependentExpr_bound
    {I : Type u} [Continuum.RealIntervalBackend I]
    (evaluator : Continuum.VerifiedExprIntervalEvaluator I)
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ)
    (hvalid : expr.ValidIteratesOn n s)
    (hindependent :
      Verified.Expr.containsVar (0 : Fin 1) (expr.symbolicDerivative n) = false)
    (input result : I)
    (hzero : Continuum.RealIntervalBackend.MemReal input 0)
    (hevaluated :
      evaluator.eval (fun _ : Fin 1 ↦ input) (expr.symbolicDerivative n) =
        some result)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    (ofIndependentExpr evaluator expr n s hvalid hindependent input result
      hzero hevaluated).bound hab hsub =
      max
        |Continuum.RealIntervalBackend.lo result|
        |Continuum.RealIntervalBackend.hi result| :=
  rfl

end Continuum.IteratedDerivativeBounderOn

end

end CAS
