/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Soundness

/-!
# Interval range providers for symbolic expressions

`VerifiedExprIntervalEvaluator I` is a partial evaluator of `Verified.Expr` into an interval
backend `I` with the inclusion property: if the environment encloses the point `ρ`, a
successful result encloses `expr.eval ρ`. `ExprIntervalContext` is an evaluator whose soundness
is fixed for one domain `s` and one interpretation `ρ` of the variables, so it may carry
variable enclosures, denominator side conditions or unary range certificates.

`ExprRangeProviderOn expr ρ s` is total: on every `[a, b] ⊆ s` with `a < b` it gives an interval
and a proof that the interval contains `expr.eval (ρ x)` for all `x ∈ [a, b]`.
`ofPanelEvaluator` builds it by evaluating on each panel.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Verified
open Set

universe u v

/--
A partial symbolic-expression interval evaluator with a proved real semantics.

The variable type is polymorphic so one evaluator implementation serves scalar,
Euclidean, and named-variable expressions.
-/
structure VerifiedExprIntervalEvaluator (I : Type u) [RealIntervalBackend I] where
  /-- Run the backend on one expression and interval environment. -/
  eval : {ι : Type v} → (ι → I) → Verified.Expr ι → Option I
  /-- Every successful run encloses evaluation of the same symbolic expression. -/
  sound :
    ∀ {ι : Type v} (env : ι → I) (ρ : ι → ℝ),
      (∀ i, RealIntervalBackend.MemReal (env i) (ρ i)) →
      ∀ {expr : Verified.Expr ι} {result : I},
        eval env expr = some result →
        RealIntervalBackend.MemReal result (expr.eval ρ)

/--
A partial symbolic interval evaluator whose soundness is already specialized
to one semantic domain and variable interpretation.
-/
structure ExprIntervalContext (I : Type u) [RealIntervalBackend I]
    {α : Type*} {ι : Type v} (s : Set α) (ρ : α → ι → ℝ) where
  /-- Run this context on a symbolic expression. -/
  eval : Verified.Expr ι → Option I
  /-- Every successful result encloses the expression at every domain point. -/
  sound :
    ∀ {expr : Verified.Expr ι} {result : I},
      eval expr = some result →
      ∀ x ∈ s, RealIntervalBackend.MemReal result (expr.eval (ρ x))

/-- Certified symbolic range production on every requested ordered real interval. -/
structure ExprRangeProviderOn {I : Type u} [RealIntervalBackend I]
    {ι : Type v} (expr : Verified.Expr ι) (ρ : ℝ → ι → ℝ) (s : Set ℝ) where
  /-- Certified output interval for the expression. -/
  result : {a b : ℝ} → a < b → Icc a b ⊆ s → I
  /-- The reported interval encloses the expression throughout its panel. -/
  sound :
    ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s)
      (x : ℝ), x ∈ Icc a b →
        RealIntervalBackend.MemReal (result hab hsub) (expr.eval (ρ x))

namespace ExprRangeProviderOn

variable {I : Type u} [RealIntervalBackend I] {ι : Type v}
  {expr : Verified.Expr ι} {ρ : ℝ → ι → ℝ} {s : Set ℝ}

/--
Evaluate an expression afresh on every requested panel.

The caller supplies only a panel-dependent variable box and proves that the
backend succeeds on those boxes. The result field is extracted from the
successful evaluator run, so no separate interval value or duplicated
evaluation equation is required.
-/
def ofPanelEvaluator
    (evaluator : VerifiedExprIntervalEvaluator I)
    (env :
      {a b : ℝ} → (hab : a < b) → Icc a b ⊆ s → ι → I)
    (henv :
      ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s)
        (x : ℝ), x ∈ Icc a b → ∀ i,
          RealIntervalBackend.MemReal (env hab hsub i) (ρ x i))
    (hsuccess :
      ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s),
        (evaluator.eval (env hab hsub) expr).isSome = true) :
    ExprRangeProviderOn (I := I) expr ρ s where
  result := fun hab hsub ↦
    (evaluator.eval (env hab hsub) expr).get (hsuccess hab hsub)
  sound := by
    intro _a _b hab hsub x hx
    exact evaluator.sound (env hab hsub) (ρ x) (henv hab hsub x hx)
      (Option.some_get (hsuccess hab hsub)).symm

end ExprRangeProviderOn

end CAS.Continuum
