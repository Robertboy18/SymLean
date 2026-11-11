/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.SideClaim
public import CAS.Polynomial.Sparse.Division

/-!
# Checked canonicalization of univariate rational expressions

`RationalCanonical.route` reduces a rational expression in one variable: a common factor of the
numerator and the denominator is cancelled, and an improper fraction is written as a polynomial
plus a proper fraction. The result is a `SideClaimRoute` whose nonzero obligations are those of
the check that accepted it; when no candidate is found or the check fails, the route is the
identity `SideClaimRoute.exact`, so it is total and sound for every input. It is the
one-coordinate case of `SidePipeline.finClaimRoute`, and the derivative bounds
`RationalInterval.compileDerivative?` and `IteratedDerivativeBounderOn.ofRationalExpr` enclose
its mixed form in interval arithmetic, where splitting off the polynomial part can remove
repeated occurrences of the variable. Rational expressions in several variables are handled by
`Alg.canonical`.

## Main definitions

* `RationalCanonical.mixedFraction`: the polynomial part plus the proper remainder of a reduced
  fraction.
* `RationalCanonical.candidate?`: the unchecked reduction candidate.
* `RationalCanonical.checkedRoute?`, `RationalCanonical.route`: the checked route, and its total
  version with the identity fallback.

## Main results

* `RationalCanonical.route_lhs`: the route starts at the input expression.
* `RationalCanonical.route_sound`: the right-hand side of the route has the value of the input
  wherever its obligations hold.

## Implementation notes

`candidate?` compiles the input to one fraction with `Alg.fractionResult`, reads both parts as
univariate sparse polynomials, takes the monic gcd from `Polynomial.Sparse.Univariate.gcd`, a
Euclidean remainder sequence whose fuel is the sum of the degrees plus two, divides both parts
by it with `Polynomial.Sparse.Univariate.divide`, insists on zero remainders, and renders the
quotient with one more long division in `mixedFraction`. None of this is proved correct.
`checkedRoute?` accepts the candidate only when `Alg.normalizeFractionWithSide (candidate - expr)`
is literally `0`; `eval_normalizeFractionWithSide` then gives the soundness proof stored in the
route, and the denominators cleared by this check are its obligations. The fraction normal form
is needed because a structural normalizer can leave an equivalent difference as `1 - q/q`,
whereas the fraction normalizer records `q ≠ 0` and checks the numerator identity. The Euclidean
gcd and long division are the classical algorithms. Since their output is only a proposal,
checked by a normalizer whose soundness is proved once, a wrong or fuel-exhausted candidate costs
a reduction and never soundness.
-/

@[expose] public section

namespace CAS.Verified.Expr

namespace RationalCanonical

/--
Render a reduced numerator and denominator in mixed rational form.

Sparse long division only proposes the form. The caller checks the resulting
expression against the original rational function before exposing a route.
-/
def mixedFraction
    (numerator denominator : Polynomial.Sparse.Univariate) :
    Verified.Expr (Fin 1) :=
  let division :=
    Polynomial.Sparse.Univariate.divide numerator denominator
  let quotient := Alg.mvPolyExpr division.quotient
  let remainder := Alg.mvPolyExpr division.remainder
  let denominatorExpr := Alg.mvPolyExpr denominator
  if division.remainder.isEmpty then
    quotient
  else if division.quotient.isEmpty then
    Verified.Expr.mkDiv remainder denominatorExpr
  else
    Verified.Expr.mkAdd quotient
      (Verified.Expr.mkDiv remainder denominatorExpr)

/--
Propose a reduced rational expression.

The input is first compiled to one fraction.  Both parts must belong to the
univariate polynomial fragment, the denominator must be nonzero, and
both exact divisions by the computed gcd must have zero remainder. The reduced
fraction is then written as a polynomial quotient plus a proper rational
remainder. This final long division is useful to interval evaluation because
it can remove repeated-variable dependency from improper rational forms.
-/
def candidate? (expr : Verified.Expr (Fin 1)) : Option (Verified.Expr (Fin 1)) := do
  let fraction := Alg.fractionResult expr
  let numerator ← Alg.mvPolyOf? fraction.num
  let denominator ← Alg.mvPolyOf? fraction.den
  let denominator := Alg.mvNormalize denominator
  if denominator.isEmpty then
    none
  else
    let common :=
      Polynomial.Sparse.Univariate.gcd numerator denominator
    if common.isEmpty then
      none
    else
      let numeratorResult :=
        Polynomial.Sparse.Univariate.divide numerator common
      let denominatorResult :=
        Polynomial.Sparse.Univariate.divide denominator common
      if numeratorResult.remainder.isEmpty &&
          denominatorResult.remainder.isEmpty then
        pure <| mixedFraction
          numeratorResult.quotient denominatorResult.quotient
      else
        none

/--
Check a proposed univariate rational reduction.

The verified single-fraction normalizer must reduce `candidate - expr` to
literal zero. Its emitted denominator conditions become the route's
obligations, and its soundness theorem supplies the proof. The
single-fraction normal form is needed here: a structural normalizer can
leave an equivalent difference as `1 - q/q`, whereas the fraction normalizer
records `q ≠ 0` and checks the numerator identity.
-/
def checkedRoute? (expr : Verified.Expr (Fin 1)) :
    Option (SideClaimRoute (Fin 1)) := do
  let candidate ← candidate? expr
  let checked := Alg.normalizeFractionWithSide (candidate - expr)
  if hzero : checked.expr = (0 : Verified.Expr (Fin 1)) then
    some
      { lhs := expr
        rhs := candidate
        nonzero := checked.nonzero
        steps :=
          [{ name := "univariate-rational-canonical"
             kind := .sideConditioned }]
        sound := by
          intro ρ hside
          have hchecked :=
            Alg.eval_normalizeFractionWithSide
              ρ (candidate - expr) hside
          rw [hzero] at hchecked
          exact sub_eq_zero.mp (by
            simpa [Verified.Expr.eval] using hchecked.symm) }
  else
    none

/--
Total checked canonicalization route.

Successful rational reductions carry their generated nonzero obligations.
Unsupported expressions and unsuccessful candidates return the identity claim
`SideClaimRoute.exact expr expr`.
-/
def route (expr : Verified.Expr (Fin 1)) : SideClaimRoute (Fin 1) :=
  (checkedRoute? expr).getD (SideClaimRoute.exact expr expr fun _ ↦ rfl)

/-- A successful checked route records the expression it was asked to reduce. -/
theorem checkedRoute?_lhs {expr : Verified.Expr (Fin 1)}
    {checked : SideClaimRoute (Fin 1)}
    (h : checkedRoute? expr = some checked) :
    checked.lhs = expr := by
  unfold checkedRoute? at h
  obtain ⟨candidate, -, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split_ifs at h
  exact Option.some.inj h ▸ rfl

/-- The total route always records the original expression as its source. -/
@[simp] theorem route_lhs (expr : Verified.Expr (Fin 1)) :
    (route expr).lhs = expr := by
  unfold route
  cases h : checkedRoute? expr with
  | none => rfl
  | some checked => exact checkedRoute?_lhs h

/-- Semantic soundness of the total route under its generated obligations. -/
theorem route_sound (expr : Verified.Expr (Fin 1)) (ρ : Fin 1 → ℝ)
    (hside : Alg.SideHolds ρ (route expr).nonzero) :
    Verified.Expr.eval ρ (route expr).rhs = Verified.Expr.eval ρ expr := by
  simpa using (route expr).sound ρ hside

end RationalCanonical

end CAS.Verified.Expr
