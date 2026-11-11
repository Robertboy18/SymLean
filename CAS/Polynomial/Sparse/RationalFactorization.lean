/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Euclidean

/-!
# Rational factors for integration

`split` lists factors of a nonzero polynomial over `ℚ` for the Hermite integration pass, which
needs factors of degree at most two. A factor of degree at most two is kept as it is, the factor
`x` is split off by exact division, and any other factor of degree three or more is split only by
a factor provider, such as the one `CASHex.Factor` registers. An unsplit factor need not be
irreducible, and no theorem relates the returned list to the input.

## Implementation notes

While a factor has degree three or more and `x` divides it, `x` is split off by exact division
(like a gcd, not a search), so `x ^ 3` gives `x` and `x ^ 2`. `split` searches for no other
factors, since factoring over `ℚ` is Hex's: `CASHex.Factor` registers Hex's Berlekamp-Zassenhaus
factorizer with `@[cas_route factor]`, which the commands and tactics read from the environment
(`Tactic.RouteRegistry.factorProvider?`) and pass on as `ofDense`. Without a provider, or when the
provider leaves a factor of degree three or more, that factor stays in the list as it is.

A provider only proposes: `split` accepts its factors only when they are proper factors (each of
degree at least one and below that of the factor) whose product is the factor (exact
multiplication and comparison), and integration checks its final output again by
differentiation.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>. Its factorizer
  `Hex.ZPoly.factorize` is the search behind the provider `CASHex.Factor.denseFactors`.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse.Univariate.RationalFactorization

open CAS

/-- A factor provider: monic factors of a monic polynomial of degree three or more, proposed by an
untrusted search (`CASHex.Factor` gives Hex's). -/
abbrev Provider := Sparse.Univariate → Option (List Sparse.Univariate)

/-- The coefficients of `p`, from the constant term up. -/
def coefficients (p : Sparse.Univariate) : Array ℚ := Id.run do
  let degree := p.foldl (fun d (_, m) ↦ max d (m 0)) 0
  let mut out : Array ℚ := Array.replicate (degree + 1) 0
  for (c, m) in p do
    out := out.set! (m 0) (out[m 0]! + c)
  return out

/-- The polynomial with the coefficients `cs`, from the constant term up. -/
def ofCoefficients (cs : Array ℚ) : Sparse.Univariate :=
  ((List.range cs.size).filterMap fun k ↦
    let c := cs.getD k 0
    if c = 0 then none else some (c, fun _ ↦ k)).reverse

/-- The provider of the factorizer `factorize`, which lists the monic irreducible factors with
their exponents of a polynomial given by its coefficients from the constant term up (the type
`Tactic.RouteRegistry.FactorProvider`): each factor repeated by its exponent, `none` for a
constant. -/
def ofDense (factorize : Array ℚ → List (Array ℚ × Nat)) : Provider := fun p ↦
  match factorize (coefficients p) with
  | [] => none
  | factors => some (factors.flatMap fun (f, e) ↦ List.replicate e (ofCoefficients f))

/-- The product of a list of polynomials, `1` for the empty list. -/
def product (factors : List Sparse.Univariate) : Sparse.Univariate :=
  factors.foldl Verified.Expr.Alg.mvMulPoly [(1, Verified.Expr.Alg.mvOne 1)]

/-- The polynomial `x`. -/
def varPoly : Sparse.Univariate :=
  [(1, Verified.Expr.Alg.mvVar (0 : Fin 1))]

/-- The factors that `provider?` proposes for the monic polynomial `p` of degree three or more,
when they are proper factors of `p` whose product is `p`. -/
def provided? (provider? : Option Provider) (p : Sparse.Univariate) :
    Option (List Sparse.Univariate) := do
  let provider ← provider?
  let factors ← provider p
  let factors := factors.map Sparse.Univariate.monic
  let degree := Sparse.Univariate.degree p
  guard (factors.length ≥ 2 &&
    factors.all (fun f ↦ 0 < Sparse.Univariate.degree f && Sparse.Univariate.degree f < degree) &&
    Verified.Expr.Alg.mvNormalize (product factors) == Verified.Expr.Alg.mvNormalize p)
  some factors

/--
Split factors until every factor has degree at most two or is not split further.

A factor of degree at most two is kept; a factor of degree three or more that `x` divides is
replaced by `x` and the quotient, which comes back to this step; any other factor of degree three
or more is replaced by the proper factors `provider?` proposes, when their product is that factor,
and kept when there are none. Fuel is
bounded by twice the input degree.
-/
def splitAux (provider? : Option Provider) :
    Nat → List Sparse.Univariate → List Sparse.Univariate → Option (List Sparse.Univariate)
  | 0, [], factors => some factors.reverse
  | 0, _, _ => none
  | _fuel + 1, [], factors => some factors.reverse
  | fuel + 1, p :: pending, factors =>
      let p := Sparse.Univariate.monic p
      if Sparse.Univariate.degree p ≤ 2 then
        splitAux provider? fuel pending (p :: factors)
      else
        -- A zero constant term splits off the factor `x` by exact division, without a search; the
        -- quotient comes back to this step while its degree is three or more.
        match Sparse.Univariate.exactQuotient? p varPoly with
        | some quotient => splitAux provider? fuel (quotient :: pending) (varPoly :: factors)
        | none =>
        match provided? provider? p with
        | some parts => splitAux provider? fuel (parts ++ pending) factors
        | none => splitAux provider? fuel pending (p :: factors)

/--
The factors of degree at most two of `p`, through `provider?` for a factor of degree three or
more, and any factor of degree three or more that is not split. `none` for the zero polynomial.
-/
def split (p : Sparse.Univariate) (provider? : Option Provider := none) :
    Option (List Sparse.Univariate) := do
  let p := Sparse.Univariate.monic p
  if Sparse.isZero p then
    none
  else if Sparse.Univariate.isOne p then
    some []
  else
    splitAux provider?
      (2 * Sparse.Univariate.degree p + 1)
      [p] []

end CAS.Polynomial.Sparse.Univariate.RationalFactorization
