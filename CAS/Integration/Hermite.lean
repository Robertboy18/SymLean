/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Integration.RationalElementary
public import CAS.Polynomial.Sparse.RationalFactorization

/-!
# Hermite reduction for rational antiderivatives

The rational part of Hermite reduction over `Rat[x]`, as a candidate generator.
`prepare?` makes the denominator monic, separates its factors by multiplicity with the
square-free decomposition `Sparse.Univariate.squareFreeFactors?` (repeated gcds and exact
quotients), and refines each stratum with `Sparse.Univariate.RationalFactorization.split`.
`candidateWith?` splits the numerator over the strata with modular inverses
(`componentNumerator?`), lowers each repeated square-free power by rational corrections
(`reducePowerAux`), and delegates the terminal square-free fraction to
`RationalElementary.candidate?`. Thus this pass handles repeated powers generically while
keeping factorization and elementary transcendental decisions independent.

## Implementation notes

We follow Hermite's note of 1872. For a square-free factor `A` of multiplicity `m ≥ 2` and a
numerator `N`, the step takes `B = -N (A')⁻¹ / (m - 1)` modulo `A` and the exact quotient `N₁`
of `N - (B' A - (m - 1) B A')` by `A`, so that `N / A ^ m = (B / A ^ (m - 1))' + N₁ / A ^ (m - 1)`,
and repeats down to `m = 1`. As in Hermite's note, the reduction needs only exact division, gcds
and inverses modulo `A`, no root of the denominator. The refinement by rational factorization
serves the logarithmic part: the closed formulas of `RationalElementary.candidate?` handle a
numerator proportional to the derivative of the factor, factors of degree at most two and the
quartics `x^4 + a*x^2 + 1`. We use neither the Horowitz-Ostrogradsky linear system nor resultants
(Rothstein-Trager).

All algebra here is candidate generation. The exact quotients only make a step fail when a
division leaves a remainder, and no theorem states the identity above or that the recurrence is
complete. `integrate?` accepts the primitive through `IntegrationCheck.certifyCandidate?` only
when the checked route `IntegrationCheck.route` reduces its derivative residual to literal zero,
and `IntegrationCheck.AntiderivativeCert.eval_diff_eq` turns that into the derivative identity
wherever the certificate's requirements hold.

## References

* Charles Hermite, "Sur l'intégration des fractions rationnelles", *Nouvelles annales de
  mathématiques*, 2e série, 11 (1872), pp. 145-148,
  <https://www.numdam.org/item/NAM_1872_2_11__145_0/>. The reduction step of `reducePowerAux`.
* Manuel Bronstein, *Symbolic Integration I: Transcendental Functions*, 2nd ed., Springer,
  Berlin, 2005, <https://doi.org/10.1007/b138171>. Chapter 2, Integration of Rational
  Functions, pp. 35-73.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.Hermite

open CAS.Polynomial

/-- The polynomial `factor.factor ^ factor.multiplicity` denoted by a square-free factor. -/
def poweredFactor
    (factor : Sparse.Univariate.SquareFreeFactor) : Sparse.Univariate :=
  Verified.Expr.Alg.mvPowPoly factor.factor (factor.multiplicity : Nat)

/--
Split a square-free factor further with the rational factorization pass, giving every
piece the original multiplicity.
-/
def refineSquareFreeFactor
    (factor : Sparse.Univariate.SquareFreeFactor)
    (provider? : Option Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (List Sparse.Univariate.SquareFreeFactor) := do
  let refined ← Sparse.Univariate.RationalFactorization.split factor.factor provider?
  some <| refined.map fun polynomial ↦
    { factor := polynomial
      multiplicity := factor.multiplicity }

/--
Numerator of the partial fraction of `numerator / denominator` over one multiplicity stratum.

With `p = poweredFactor factor` and `denominator = p * cofactor`, the result is
`numerator * cofactor⁻¹` reduced modulo `p`, the inverse also being taken modulo `p`. A
failing exact division or modular inverse returns `none`.
-/
def componentNumerator? (numerator denominator : Sparse.Univariate)
    (factor : Sparse.Univariate.SquareFreeFactor) : Option Sparse.Univariate := do
  let powered := poweredFactor factor
  let cofactor ← Sparse.Univariate.exactQuotient? denominator powered
  let inverse ← Sparse.Univariate.inverseMod? cofactor powered
  Sparse.Univariate.modulo?
    (Verified.Expr.Alg.mvMulPoly numerator inverse) powered

/--
Lower `numerator / factor ^ exponent` to a square-free fraction by repeated Hermite steps.

`factorDerivative` is the derivative of `factor` and `inverseDerivative` its inverse modulo
`factor`. Each step at exponent `m ≥ 2` emits the correction `B / factor ^ (m - 1)` and
continues with the next numerator at exponent `m - 1`; the list argument accumulates these
corrections most recent first. The result pairs the final numerator over `factor` with the
corrections in production order. Exponent `0` returns `none`.
-/
def reducePowerAux (factor factorDerivative inverseDerivative : Sparse.Univariate) :
    Nat → Sparse.Univariate → List (Verified.Expr (Fin 1)) →
      Option (Sparse.Univariate × List (Verified.Expr (Fin 1)))
  | 0, _, _ => none
  | 1, numerator, corrections =>
      some (Verified.Expr.Alg.mvNormalize numerator, corrections.reverse)
  | exponent + 2, numerator, corrections => do
      let lowerExponent := exponent + 1
      /-
      For `m = lowerExponent + 1`, this branch is designed to maintain

        N / f^m = d(B / f^(m - 1)) + Nnext / f^(m - 1).

      It chooses `B = -N * (f')⁻¹ / (m - 1)` modulo `f`, then exact-divides
      `N - (B' * f - (m - 1) * B * f')` by `f` to obtain `Nnext`. The
      exact quotient checks divisibility, but no theorem here proves the displayed
      rational-function identity; the candidate is accepted only after
      differentiation and residual normalization.
      -/
      let correctionNumerator ←
        Sparse.Univariate.modulo?
          (Sparse.scale
            (-(1 / (lowerExponent : Rat)))
            (Verified.Expr.Alg.mvMulPoly numerator inverseDerivative))
          factor
      let derivativeNumerator :=
        Verified.Expr.Alg.mvSub
          (Verified.Expr.Alg.mvMulPoly
            (Sparse.derivative (0 : Fin 1) correctionNumerator) factor)
          (Sparse.scale (lowerExponent : Rat)
            (Verified.Expr.Alg.mvMulPoly
              correctionNumerator factorDerivative))
      let nextNumerator ←
        Sparse.Univariate.exactQuotient?
          (Verified.Expr.Alg.mvSub numerator derivativeNumerator)
          factor
      let correction :=
        Verified.Expr.simplifyDiv
          (Verified.Expr.Alg.mvPolyExpr correctionNumerator)
          (Verified.Expr.Alg.mvPolyExpr
            (Verified.Expr.Alg.mvPowPoly factor lowerExponent))
      reducePowerAux factor factorDerivative inverseDerivative
        lowerExponent nextNumerator (correction :: corrections)

/--
Antiderivative candidate for `numerator / factor.factor ^ factor.multiplicity`.

Multiplicity `1` is passed directly to `RationalElementary.candidate?`. Otherwise
`reducePowerAux` lowers the power to `1`, and the corrections are summed with the primitive
of the remaining square-free fraction. A missing modular inverse of the factor derivative
or a failing exact division returns `none`.
-/
def repeatedFactorCandidate?
    (factor : Sparse.Univariate.SquareFreeFactor)
    (numerator : Sparse.Univariate) : Option (Verified.Expr (Fin 1)) := do
  if (factor.multiplicity : Nat) = 1 then
    RationalElementary.candidate? numerator factor.factor
  else
    let factorDerivative :=
      Sparse.derivative (0 : Fin 1) factor.factor
    let inverseDerivative ←
      Sparse.Univariate.inverseMod? factorDerivative factor.factor
    let reduced ←
      reducePowerAux factor.factor factorDerivative inverseDerivative
        (factor.multiplicity : Nat) numerator []
    let squareFreePrimitive ←
      RationalElementary.candidate? reduced.1 factor.factor
    some <| Verified.Expr.mkAddList (reduced.2 ++ [squareFreePrimitive])

/--
The denominator data of Hermite reduction: the leading coefficient, the monic denominator and
its refined square-free strata. Several numerators over one denominator share it.
-/
structure Prepared where
  /-- The leading coefficient of the denominator. -/
  leading : Rat
  /-- The denominator divided by its leading coefficient. -/
  monicDenominator : Sparse.Univariate
  /-- The square-free strata of the monic denominator, refined by rational factorization. -/
  factors : List Sparse.Univariate.SquareFreeFactor

/-- Decompose a denominator once for `candidateWith?`. -/
def prepare? (denominator : Sparse.Univariate)
    (provider? : Option Sparse.Univariate.RationalFactorization.Provider := none) :
    Option Prepared := do
  let leading ← Verified.Expr.Alg.mvLeadingTermNormalized? denominator
  let monicDenominator :=
    Sparse.scale (1 / leading.1) denominator
  let factors ←
    Sparse.Univariate.squareFreeFactors? monicDenominator
  let factors ← factors.flatMapM (refineSquareFreeFactor · provider?)
  some { leading := leading.1, monicDenominator, factors }

/-- Hermite reduction of `numerator / denominator` from the prepared denominator data. -/
def candidateWith? (prepared : Prepared) (numerator : Sparse.Univariate) :
    Option (Verified.Expr (Fin 1)) := do
  let monicNumerator :=
    Sparse.scale (1 / prepared.leading) numerator
  let primitives ← prepared.factors.mapM fun factor ↦ do
    let numerator ←
      componentNumerator? monicNumerator prepared.monicDenominator factor
    repeatedFactorCandidate? factor numerator
  some (Verified.Expr.mkAddList primitives)

/--
Hermite-reduction candidate for a proper rational fraction.

The denominator may have several coprime multiplicity strata. Unsupported
terminal square-free factors cause conservative failure. A zero numerator over a nonzero
denominator returns `0` before the denominator is decomposed.
-/
def candidate? (numerator denominator : Sparse.Univariate)
    (provider? : Option Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (Verified.Expr (Fin 1)) := do
  if Sparse.isZero numerator then
    guard !(Sparse.isZero denominator)
    return 0
  candidateWith? (← prepare? denominator provider?) numerator

end CAS.IntegrationPlanner.Hermite
