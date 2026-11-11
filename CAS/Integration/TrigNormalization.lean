/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Configured

/-!
# Checked trigonometric-polynomial normalization for integration

Power-reduction antiderivatives leave polynomial residuals in `sin u` and
`cos u`. The ordinary exact pipeline recognizes local Pythagorean identities,
but higher powers need one canonical elimination step before polynomial
normalization. `route` is the second stage of `IntegrationCheck.route`: two rounds of
`trigPolynomialClaimRoute`, then the general side-conditioned route
`Verified.Expr.simplifySideClaimRoute` when they do not reach zero.

## Implementation notes

We run the shared Pythagorean pass of the checked normalizer,
`CAS.Verified.Expr.pythagoreanSidePass`, which replaces one pair of cosine factors, or one square
of a power `cos u ^ n` with `n ≥ 2`, at each product or power node outside denominators,
radicands, logarithm arguments and real powers, through `cos u ^ 2 = 1 - sin u ^ 2`, and then
invoke the checked algebra normalizer `Verified.Expr.Alg.normalize`. Two rounds expose the
residuals of reduced powers. The `sound` field of each round is the soundness of the pass
composed with that of the normalizer, so the stage is itself a `Verified.Expr.SideClaimRoute`
and joins the checked route by `Verified.Expr.SideClaimRoute.trans`.

The route is local to antiderivative checking. It does not rewrite the output
of the general simplifier or choose how user-facing trigonometric expressions
are presented; the pass itself is documented in
`CAS.ClosedForm.Pipeline.Passes.Pythagorean`.
-/

@[expose] public section

namespace CAS.IntegrationCheck.TrigNormalization

open CAS.Verified.Expr CAS.Verified.Expr

/-- Checked claim that rewrites the cosine squares of an expression with one run of the
Pythagorean pass and polynomially normalizes the result. The pass records no obligation. -/
def trigPolynomialClaimRoute {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : Verified.Expr.SideClaimRoute ι :=
  let rewritten := (pythagoreanSidePass (ι := ι)).run expr
  { lhs := expr
    rhs := Alg.normalize rewritten.expr
    nonzero := rewritten.nonzero
    steps :=
      [{ name := (pythagoreanSidePass (ι := ι)).name, kind := .checked },
       { name := "algebra", kind := .checked }]
    sound := by
      intro rho hside
      calc
        (Alg.normalize rewritten.expr).eval rho = rewritten.expr.eval rho := by simp
        _ = expr.eval rho := (pythagoreanSidePass (ι := ι)).sound rho expr hside }

/-- Run two checked rewrite-normalize rounds, enough to expose reduced power residuals. -/
def trigPolynomialClaimRouteTwice {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : Verified.Expr.SideClaimRoute ι :=
  let first := trigPolynomialClaimRoute expr
  first.trans (trigPolynomialClaimRoute first.rhs) rfl

/-- Normalize a trigonometric residual, using the general checked route as a fallback. -/
def route {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : Verified.Expr.SideClaimRoute ι :=
  let trigonometric := trigPolynomialClaimRouteTwice expr
  if trigonometric.rhs = 0 then
    trigonometric
  else
    trigonometric.trans (Verified.Expr.simplifySideClaimRoute trigonometric.rhs) rfl

/-- Trigonometric residual normalization retains the supplied expression as its source. -/
@[simp] theorem route_lhs
    {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    (route expr).lhs = expr := by
  simp only [route]
  split <;> rfl

end CAS.IntegrationCheck.TrigNormalization
