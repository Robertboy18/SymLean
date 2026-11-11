/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Rational
public import CAS.Expr.Decomposition

/-!
# Checked proportionality of symbolic expressions

`Alg.proportionality? target source` searches for a factor `c` with `target = c * source` and
returns it in a `NormResult` whose `nonzero` list holds the denominator conditions of the
identity; `Alg.proportionality?_sound` proves `target = c * source` wherever they hold.
`IntegrationPlanner.RationalElementary.candidate?` uses it to recognize a numerator that is a
constant multiple of the derivative of the denominator, whose primitive is a logarithm.

## Main definitions

* `Alg.proportionalityFactorCandidate?`: the unchecked candidate factor.
* `Alg.proportionality?`: the checked factor together with its denominator conditions.

## Main results

* `Alg.proportionality?_sound`: every returned factor satisfies `target = c * source` at the
  valuations where its conditions hold.

## Implementation notes

The candidate comes from the fraction normal form of `target / source`. When this is a quotient,
possibly times a factor that is moved into the numerator, `polynomialProportionalityFactor?`
takes the first nonzero term of the denominator, divides the coefficient of the same monomial in
the numerator by its coefficient, and keeps the ratio `c` only if `Alg.normalize` reduces
`numerator - c * denominator` to `0`. Otherwise `singleMonomialQuotient?` handles a numerator and
a denominator that are single monomials: it divides the coefficients and cancels the common
opaque factors as multisets (`cancelMonomialFactors`). Any other normal form is proposed as it
stands. The search is not proved correct: `proportionality?` accepts a candidate only when
`Alg.normalizeFractionWithSide (target - c * source)` is literally `0`, and
`proportionality?_sound` follows from `eval_normalizeFractionWithSide`, with the denominators
cleared by this check as the conditions.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr.Alg

/-- The first term of a polynomial whose rational coefficient is nonzero, if there is one. -/
def firstNonzeroTerm? {ι : Type*} :
    Poly ι → Option (Rat × Monomial ι)
  | [] => none
  | term :: rest =>
      if term.1 = 0 then firstNonzeroTerm? rest else some term

/-- The unique term of a polynomial with nonzero coefficient, or `none` when the polynomial has
no such term or more than one. -/
def singleNonzeroTerm? {ι : Type*} :
    Poly ι → Option (Rat × Monomial ι)
  | [] => none
  | term :: rest =>
      if term.1 = 0 then
        singleNonzeroTerm? rest
      else
        match firstNonzeroTerm? rest with
        | none => some term
        | some _ => none

/-- Coefficient of the first term whose factor list is a permutation of `monomial`, if any. -/
def coefficientOfMonomial? {ι : Type*} [DecidableEq ι]
    (monomial : Monomial ι) :
    Poly ι → Option Rat
  | [] => none
  | term :: rest =>
      if term.2.Perm monomial then
        some term.1
      else
        coefficientOfMonomial? monomial rest

/-- Discover a rational factor between two normalized opaque-factor polynomials.

The first nonzero denominator term proposes the coefficient ratio; ordinary normalization checks
every remaining term before the factor is returned. -/
def polynomialProportionalityFactor? {ι : Type*} [DecidableEq ι]
    (target source : Verified.Expr ι) : Option Rat := do
  let targetPoly := normalizePoly (polyOf target)
  let sourcePoly := normalizePoly (polyOf source)
  match firstNonzeroTerm? sourcePoly with
  | none => none
  | some sourceTerm => do
      let targetCoefficient ← coefficientOfMonomial? sourceTerm.2 targetPoly
      if sourceTerm.1 = 0 then
        none
      else
        let factor := targetCoefficient / sourceTerm.1
        let residual := normalize (target - mkRatConst factor * source)
        if residual = 0 then some factor else none

/-- Cancel the common opaque factors of a numerator and a denominator monomial as multisets.

Each denominator factor is erased once from the numerator when it occurs there; the factors that
cannot be cancelled form the remaining denominator. -/
def cancelMonomialFactors {ι : Type*} [DecidableEq ι] :
    Monomial ι → Monomial ι → Monomial ι × Monomial ι
  | numerator, [] => (numerator, [])
  | numerator, factor :: denominator =>
      match removeFactor? factor numerator with
      | some numerator' => cancelMonomialFactors numerator' denominator
      | none =>
          let rest := cancelMonomialFactors numerator denominator
          (rest.1, factor :: rest.2)

/-- Propose an exact quotient of two single normalized monomials.

Rational coefficients are divided exactly and common opaque factors are cancelled as multisets.
The result remains only a proposal until `proportionality?` checks the reconstructed identity. -/
def singleMonomialQuotient? {ι : Type*} [DecidableEq ι]
    (numerator denominator : Verified.Expr ι) :
    Option (Verified.Expr ι) := do
  let numeratorTerm ← singleNonzeroTerm? (normalizePoly (polyOf numerator))
  let denominatorTerm ← singleNonzeroTerm? (normalizePoly (polyOf denominator))
  if denominatorTerm.1 = 0 then
    none
  else
    let remaining := cancelMonomialFactors numeratorTerm.2 denominatorTerm.2
    let rationalFactor := mkRatConst (numeratorTerm.1 / denominatorTerm.1)
    let symbolicFactor := simplifyDiv (monoExpr remaining.1) (monoExpr remaining.2)
    some (simplifyMul rationalFactor symbolicFactor)

/-- Propose a factor `c` with `target = c * source`; the proposal is not checked here.

The quotient `target / source` is fraction-normalized. When the result is a quotient of
polynomials, possibly times a coefficient, a rational factor or an exact single-monomial
quotient is proposed. Any other normalized shape is returned as the candidate itself. -/
def proportionalityFactorCandidate? {ι : Type*} [DecidableEq ι]
    (target source : Verified.Expr ι) :
    Option (Verified.Expr ι) :=
  let quotient := (normalizeFractionWithSide (target / source)).expr
  match quotient with
  | .mul coefficient (.div numerator denominator) =>
      let numerator := simplifyMul coefficient numerator
      match polynomialProportionalityFactor? numerator denominator with
      | some factor => some (mkRatConst factor)
      | none => singleMonomialQuotient? numerator denominator
  | .mul (.div numerator denominator) coefficient =>
      let numerator := simplifyMul coefficient numerator
      match polynomialProportionalityFactor? numerator denominator with
      | some factor => some (mkRatConst factor)
      | none => singleMonomialQuotient? numerator denominator
  | .div numerator denominator =>
      match polynomialProportionalityFactor? numerator denominator with
      | some factor => some (mkRatConst factor)
      | none => singleMonomialQuotient? numerator denominator
  | expr => some expr

/-- Try to discover and certify a symbolic proportionality factor.

The candidate is accepted only when fraction normalization reduces
`target - factor * source` to zero. The `expr` field of the returned
`NormResult` is the checked factor; its `nonzero` field contains precisely the
denominator conditions needed for the identity. -/
def proportionality? {ι : Type*} [DecidableEq ι]
    (target source : Verified.Expr ι) :
    Option (NormResult ι) :=
  match proportionalityFactorCandidate? target source with
  | none => none
  | some factor =>
      let checked := normalizeFractionWithSide (target - factor * source)
      if checked.expr = 0 then
        some { expr := factor, nonzero := checked.nonzero }
      else
        none

/-- Every returned proportionality result proves the represented identity. -/
theorem proportionality?_sound {ι : Type*} [DecidableEq ι]
    {target source : Verified.Expr ι}
    {result : NormResult ι}
    (hresult : proportionality? target source = some result)
    (ρ : ι → ℝ)
    (hside : SideHolds ρ result.nonzero) :
    target.eval ρ = result.expr.eval ρ * source.eval ρ := by
  unfold proportionality? at hresult
  split at hresult
  · cases hresult
  · next factor _ =>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hresult
    obtain ⟨hzero, rfl⟩ := hresult
    have h := eval_normalizeFractionWithSide ρ (target - factor * source) hside
    rw [hzero] at h
    exact sub_eq_zero.mp (h.symm.trans (Nat.cast_zero (R := ℝ)))

end Verified.Expr.Alg
end CAS
