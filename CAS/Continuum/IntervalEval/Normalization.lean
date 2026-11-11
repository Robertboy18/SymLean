/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.AdvancedPasses
public import CAS.Expr.Simplify
public import CAS.Polynomial.Sparse.Semantics

/-!
# Lightweight exact normalization for interval evaluation

Interval evaluation uses a small checked part of the simplification pipeline of the computer
algebra system. `intervalNormalizeWithSide` applies trigonometric simplification, cancels the
factors that the numerator and denominator of a top-level quotient share, and records every
nonzero side condition the cancellation needs; `eval_intervalNormalizeWithSide` shows that the
value is unchanged when these conditions hold. Numerical code may use the result only after its
interval registry proves them. `normalizePolynomialFragments` normalizes polynomial
subexpressions and keeps natural powers as power nodes, so the interval backend can use its
parity-aware power enclosure instead of expanding the expression.

## Implementation notes

Both normalizers run inside the CEGA planner, so the kernel reduces them in every query that
reaches them. The full side-condition pipeline (`Verified.Expr.sideConditionPipeline`) runs its
side passes around a fixed-point base pipeline, up to `Verified.Expr.defaultFuel` rounds of
`Verified.Expr.checkedPasses`; we run two of its passes once each. `Verified.Expr.trigSimplify`,
the trigonometric pass of the base pipeline, is one structural recursion with local
simplification and trigonometric identities. The side pass
`Verified.Expr.deepFactorCancelCleanup` acts only when the result is a quotient: it cancels each
factor of the denominator's product tree that it finds in the numerator and records the factors
of every canceled one (`Expr.Alg.sideFactors`) as nonzero obligations, which
`Expr.Alg.cleanSide` deduplicates. The evaluation theorem composes
`Verified.Expr.eval_trigSimplify` with `Verified.Expr.eval_deepFactorCancelCleanup`. The callers
prove the obligations: `CertifiedEvalContext.evalNormalized` on the chart, and the monotonicity
route for a partial derivative (`CertifiedEvalRegistry.partialSideRoute`).

`normalizePolynomialFragments` is a structural recursion that applies
`Verified.Expr.Alg.mvNormalizeExpr` at every sum, difference, product, negation and natural power
after normalizing the children, and only recurses through quotients, the elementary functions
and real powers; outside the polynomial fragment `mvNormalizeExpr` returns its input. Its
equation is unconditional, so it emits no side conditions.
`CAS.Continuum.IntervalEval.Registry.Monotonicity` applies it to partial derivatives
(`CertifiedEvalRegistry.algebraicPartialAttempt?`).
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open CAS.Verified

/--
Normalize every polynomial subexpression with `mvNormalizeExpr`, leaving the other heads in
place.

Sparse reification keeps natural powers. Applying it recursively combines polynomial terms
inside rational or transcendental expressions without turning `x ^ 4` into a four-factor
interval product.
-/
def normalizePolynomialFragments {n : Nat} :
    Verified.Expr (Fin n) → Verified.Expr (Fin n)
  | .add a b =>
      Verified.Expr.Alg.mvNormalizeExpr
        (.add (normalizePolynomialFragments a) (normalizePolynomialFragments b))
  | .mul a b =>
      Verified.Expr.Alg.mvNormalizeExpr
        (.mul (normalizePolynomialFragments a) (normalizePolynomialFragments b))
  | .sub a b =>
      Verified.Expr.Alg.mvNormalizeExpr
        (.sub (normalizePolynomialFragments a) (normalizePolynomialFragments b))
  | .div a b => .div (normalizePolynomialFragments a) (normalizePolynomialFragments b)
  | .neg a => Verified.Expr.Alg.mvNormalizeExpr (.neg (normalizePolynomialFragments a))
  | .pow a k =>
      Verified.Expr.Alg.mvNormalizeExpr (.pow (normalizePolynomialFragments a) k)
  | .sin a => .sin (normalizePolynomialFragments a)
  | .cos a => .cos (normalizePolynomialFragments a)
  | .atan a => .atan (normalizePolynomialFragments a)
  | .asin a => .asin (normalizePolynomialFragments a)
  | .acos a => .acos (normalizePolynomialFragments a)
  | .exp a => .exp (normalizePolynomialFragments a)
  | .log a => .log (normalizePolynomialFragments a)
  | .sqrt a => .sqrt (normalizePolynomialFragments a)
  | .rpow a b => .rpow (normalizePolynomialFragments a) (normalizePolynomialFragments b)
  | expr => expr

/-- Recursive sparse-polynomial fragment normalization preserves evaluation. -/
@[simp] theorem eval_normalizePolynomialFragments {n : Nat} (x : ℝ^n) :
    ∀ expr : Verified.Expr (Fin n),
      (normalizePolynomialFragments expr).eval x = expr.eval x := by
  intro expr
  induction expr <;>
    simp [normalizePolynomialFragments, Verified.Expr.Alg.eval_mvNormalizeExpr, *]

/-- Simplify locally, close elementary trigonometric identities, and cancel the factors shared by
the numerator and denominator of a top-level quotient (`deepFactorCancelCleanup`), retaining
every nonzero obligation emitted by cancellation. -/
def intervalNormalizeWithSide {ι : Type*} [DecidableEq ι]
    (expr : Expr ι) : Expr.Alg.NormResult ι :=
  let simplified := expr.trigSimplify
  let canceled := Verified.Expr.deepFactorCancelCleanup simplified
  { expr := canceled.expr
    nonzero := Expr.Alg.cleanSide canceled.nonzero }

/-- The lightweight interval normalizer preserves evaluation whenever all of
its emitted side conditions hold. -/
theorem eval_intervalNormalizeWithSide {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr : Expr ι)
    (hside : Expr.Alg.SideHolds ρ (intervalNormalizeWithSide expr).nonzero) :
    (intervalNormalizeWithSide expr).expr.eval ρ = expr.eval ρ :=
  (Verified.Expr.eval_deepFactorCancelCleanup ρ expr.trigSimplify
    (Expr.Alg.sideHolds_of_cleanSide hside)).trans (Expr.eval_trigSimplify ρ expr)

end CAS.Continuum.RationalInterval
