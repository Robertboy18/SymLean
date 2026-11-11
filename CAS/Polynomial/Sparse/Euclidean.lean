/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Division
public import CAS.Polynomial.Sparse

/-!
# Exact univariate Euclidean algorithms

Euclidean-algebra operations on the canonical sparse rational polynomial representation:
the exact quotient `exactQuotient?`, the remainder `modulo?`, the extended Euclidean algorithm
`extendedGcdCandidate` with `bezoutCoefficientsCandidate?`, the modular inverse `inverseMod?`,
and the square-free decomposition `squareFreeFactors?`.

## Implementation notes

These routines generate candidates, and no theorem is stated about their output. A client
checks the identities it relies on; `RadicalCertificate.valid`, for example, checks the
divisibility relations and the Bézout identity of a proposed square-free radical.

For the square-free decomposition we use the classical iteration of gcds and exact quotients over
`ℚ`. With `r = gcd(p, p')` for the monic input `p`, the quotient `w = p / r` is the product of the
distinct irreducible factors of `p`. Each step takes `gcd(w, r)`, the product of those of
multiplicity above the current one: `w` divided by it is the product of those of the current
multiplicity, and `r` divided by it has every exponent lowered by one. No derivative is taken after
the first step. The loops run on fuel computed from the degrees of their inputs, and a failing exact
quotient makes the whole decomposition fail.

`squareFreeFactors?` is in the core library, although Hex decomposes square-free parts too, since
core modules call it: `RadicalCertificate.candidate?` proposes the square-free radicals of the root
certificates with it (for `RadicalCertificate.generate?`), `CAS.IntegrationPlanner.Hermite.prepare?`
separates the factors of a denominator by multiplicity with it, and so do
`CAS.IntegrationPlanner.Rational.needsFactorProvider` and the root splitter
`CAS.Command.RootSplit.split`.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse.Univariate

open CAS

/-- Decide whether a sparse polynomial is the canonical constant one. -/
def isOne (p : Sparse.Univariate) : Bool :=
  decide (Verified.Expr.Alg.mvNormalize p = Sparse.monomial 1 0)

/-- Exact polynomial quotient, failing when the remainder is nonzero. -/
def exactQuotient? (dividend divisor : Sparse.Univariate) : Option Sparse.Univariate :=
  if Sparse.isZero divisor then
    none
  else
    let result :=
      Sparse.Univariate.divide dividend divisor
    if Sparse.isZero result.remainder then
      some (Verified.Expr.Alg.mvNormalize result.quotient)
    else
      none

/-- Canonical remainder modulo a nonzero polynomial. -/
def modulo? (dividend modulus : Sparse.Univariate) : Option Sparse.Univariate :=
  if Sparse.isZero modulus then
    none
  else
    some <| Verified.Expr.Alg.mvNormalize
      (Sparse.Univariate.divide dividend modulus).remainder

/-- Untrusted output of the extended Euclidean algorithm: a monic gcd candidate together with
candidate Bézout coefficients for the two inputs. -/
structure ExtendedGcdCandidate where
  /-- Monic candidate for the greatest common divisor of the two inputs. -/
  gcd : Sparse.Univariate
  /-- Candidate coefficient of the first input in the Bézout identity. -/
  left : Sparse.Univariate
  /-- Candidate coefficient of the second input in the Bézout identity. -/
  right : Sparse.Univariate
deriving DecidableEq

/-- Scale a gcd candidate and its Bézout coefficients by the inverse of the gcd's leading
coefficient so that the candidate is monic. A zero gcd yields the all-zero candidate. -/
def normalizeExtendedGcd
    (gcd left right : Sparse.Univariate) : ExtendedGcdCandidate :=
  match Verified.Expr.Alg.mvLeadingTermNormalized? gcd with
  | none =>
      { gcd := Sparse.zero
        left := Sparse.zero
        right := Sparse.zero }
  | some leading =>
      let inverse := 1 / leading.1
      { gcd := Sparse.scale inverse gcd
        left := Sparse.scale inverse left
        right := Sparse.scale inverse right }

/-- Fuel-bounded extended Euclidean loop.

After the fuel argument come the consecutive remainders `oldR, r` and the consecutive
Bézout coefficient pairs `oldS, s` and `oldT, t`. The loop stops when `r` is zero or the fuel
is exhausted and returns the normalized state of the previous step. -/
def extendedGcdAux :
    Nat → Sparse.Univariate → Sparse.Univariate →
      Sparse.Univariate → Sparse.Univariate →
        Sparse.Univariate → Sparse.Univariate → ExtendedGcdCandidate
  | 0, oldR, _, oldS, _, oldT, _ =>
      normalizeExtendedGcd oldR oldS oldT
  | fuel + 1, oldR, r, oldS, s, oldT, t =>
      if Sparse.isZero r then
        normalizeExtendedGcd oldR oldS oldT
      else
        let division :=
          Sparse.Univariate.divide oldR r
        let quotient := division.quotient
        extendedGcdAux fuel
          r division.remainder
          s (Verified.Expr.Alg.mvSub oldS
            (Verified.Expr.Alg.mvMulPoly quotient s))
          t (Verified.Expr.Alg.mvSub oldT
            (Verified.Expr.Alg.mvMulPoly quotient t))

/-- Run the extended Euclidean algorithm on the normalized inputs `a` and `b` with fuel
`degree a + degree b + 2`, starting from the identity Bézout coefficients. -/
def extendedGcdCandidate
    (a b : Sparse.Univariate) : ExtendedGcdCandidate :=
  extendedGcdAux
    (Sparse.Univariate.degree a + Sparse.Univariate.degree b + 2)
    (Verified.Expr.Alg.mvNormalize a)
    (Verified.Expr.Alg.mvNormalize b)
    (Sparse.monomial 1 0) Sparse.zero Sparse.zero (Sparse.monomial 1 0)

/--
Propose coefficients `(left, right)` for a Bézout identity
`left * a + right * b = 1`.

The pair is returned only when the internal extended-Euclidean candidate has
constant gcd one. The identity itself remains untrusted and must be checked by
the theorem-facing caller.
-/
def bezoutCoefficientsCandidate?
    (a b : Sparse.Univariate) :
    Option (Sparse.Univariate × Sparse.Univariate) :=
  let candidate := extendedGcdCandidate a b
  if isOne candidate.gcd then
    some (candidate.left, candidate.right)
  else
    none

/--
Candidate inverse of `a` modulo `modulus`.

Clients requiring a certified inverse must check the modular product identity.
-/
def inverseMod? (a modulus : Sparse.Univariate) : Option Sparse.Univariate := do
  if Sparse.isZero modulus then
    none
  let coefficients ← bezoutCoefficientsCandidate? a modulus
  modulo? coefficients.1 modulus

/--
Candidate nonconstant square-free factor together with its intended
multiplicity.
-/
structure SquareFreeFactor where
  /-- Candidate nonconstant square-free factor of the normalized input. -/
  factor : Sparse.Univariate
  /-- Intended positive exponent of `factor` in the input's factorization. -/
  multiplicity : ℕ+
deriving DecidableEq

/-- Fuel-bounded loop of the square-free decomposition `squareFreeFactors?`.

The state is the current multiplicity, the square-free product `w`, the repeated-factor
product `repeated`, and the factors collected so far in reverse order. Each step splits off
one candidate factor by exact quotients; a failing exact quotient aborts the decomposition. -/
def squareFreeAux :
    Nat → ℕ+ → Sparse.Univariate → Sparse.Univariate → List SquareFreeFactor →
      Option (List SquareFreeFactor)
  | 0, _, w, _, factors =>
      if isOne w then some factors.reverse else none
  | fuel + 1, multiplicity, w, repeated, factors =>
      if isOne w then
        some factors.reverse
      else
        /-
        In characteristic zero, if the square-free multiplicity factors are
        `f_i`, the intended state invariant is

          w_i        = product of f_j for j >= i,
          repeated_i = product of f_j^(j - i) for j >= i.

        Hence `gcd(w_i, repeated_i) = w_(i+1)` and
        `w_i / w_(i+1) = f_i`. Here `current` is that candidate `f_i`;
        `common` and `repeated'` advance the two products. Exact quotients
        check the requested divisions; reconstruction, square-freeness,
        coprimality, and multiplicities are left to the caller's checker.
        -/
        let common :=
          Sparse.Univariate.gcd w repeated
        do
          let current ← exactQuotient? w common
          let repeated' ← exactQuotient? repeated common
          let factors' :=
            if isOne current then
              factors
            else
              { factor := current
                multiplicity := multiplicity } :: factors
          let nextMultiplicity : ℕ+ :=
            ⟨(multiplicity : Nat) + 1, by omega⟩
          squareFreeAux fuel nextMultiplicity
            common repeated' factors'

/--
Square-free decomposition of a nonzero univariate polynomial by repeated gcds and exact
quotients.

The input is made monic. A successful result is candidate factor data indexed
by intended multiplicity. Reconstruction of the monic input, square-freeness of each factor,
coprimality of distinct factors, and completeness of the list are properties for the caller to
check.
-/
def squareFreeFactors? (p : Sparse.Univariate) : Option (List SquareFreeFactor) := do
  let p := Sparse.Univariate.monic p
  if Sparse.isZero p then
    none
  else
    let repeated :=
      Sparse.Univariate.gcd p
        (Sparse.derivative (0 : Fin 1) p)
    let squareFree ← exactQuotient? p repeated
    squareFreeAux
      (Sparse.Univariate.degree p + 1)
      ⟨1, by omega⟩ squareFree repeated []

end CAS.Polynomial.Sparse.Univariate
