/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Substitution
public import CAS.Integration.Hermite
public import CAS.Integration.Polynomial

/-!
# Univariate rational antiderivative candidates

Exact polynomial quotient extraction for rational functions in one variable, by the sparse
Euclidean division `Polynomial.Sparse.Univariate.divide`:

```text
numerator = quotient * denominator + remainder.
```

`candidate?` puts the fraction in lowest terms (`lowestTerms`), integrates the quotient with the
multivariate polynomial planner `Polynomial.candidate?`, and passes the proper part to the
Hermite layer `Hermite.candidate?`, which separates denominator multiplicities, lowers repeated
square-free powers by rational corrections, and delegates the terminal square-free remainder to
the elementary rational planner. `rationalDenominatorCandidateIn?` integrates in any coordinate
a fraction whose denominator has rational coefficients, keeping parameter-dependent numerator
coefficients outside the univariate calculation; `Parameterized.candidate?` handles linear and
quadratic denominators with symbolic coefficients. `candidateIn?` tries the two in this order.

## Implementation notes

Inside each square-free stratum, a factor of degree at most two is kept, `x` is split off a factor
of degree three or more while it divides it, and any other factor of degree three or more needs a
factor provider (`RationalFactorization.split`): Hex's factorizer, which `CASHex.Factor` installs.
Without it such a factor stays whole, and the integrand is refused unless
`RationalElementary.candidate?` handles that factor (a numerator proportional to its derivative,
or a quartic `x^4 + a*x^2 + 1`); the refusal of the integration command and tactic then carries
the hint that `needsFactorProvider` decides. Terminal quadratics support both arctangent and real
logarithmic branches, with symbolic square roots when the scale is irrational. Other irreducible
factors of degree three or more are not handled; they would need algebraic numbers and real-root
isolation.

`Parameterized.divideCoefficients` divides as if the leading coefficient of the divisor were
nonzero, and `Parameterized.candidate?` takes the arctangent branch of a quadratic as if
`4*a*c - b^2 > 0`; neither is checked here. As with every integration planner, the candidate is
accepted only after the integration checker differentiates it back to the original expression:
`IntegrationCheck.certifyCandidate?` needs `IntegrationCheck.route` to reduce the residual to
literal zero. The checker exposes checked compact nonzero conditions and any required strict
positivity conditions, so the two assumptions above become requirements of the certificate. Its
soundness proof recovers the exact raw route conditions before applying the derivative
certificate. -/

@[expose] public section

namespace CAS.IntegrationPlanner.Rational

/--
The fraction `numerator / denominator` in lowest terms: both divided by their monic greatest
common divisor. A substituted integrand often keeps a common factor (the tangent half-angle
substitution turns `1 / (2 + cos x)` into `2 (1 + u²) / ((1 + u²) (3 + u²))`), and the reduced
denominator is the one whose factors the rational integrator can split.
-/
def lowestTerms (numerator denominator : CAS.Polynomial.Sparse.Univariate) :
    CAS.Polynomial.Sparse.Univariate × CAS.Polynomial.Sparse.Univariate :=
  let common :=
    (Polynomial.Sparse.Univariate.extendedGcdCandidate numerator denominator).gcd
  if Polynomial.Sparse.Univariate.degree common = 0 then
    (numerator, denominator)
  else
    match Polynomial.Sparse.Univariate.exactQuotient? numerator common,
        Polynomial.Sparse.Univariate.exactQuotient? denominator common with
    | some reducedNumerator, some reducedDenominator => (reducedNumerator, reducedDenominator)
    | _, _ => (numerator, denominator)

/--
Candidate antiderivative obtained by exact univariate polynomial division and
integration of the proper remainder, after the fraction is put in lowest terms.
-/
def candidate? (expr : Verified.Expr (Fin 1))
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (Verified.Expr (Fin 1)) := do
  let fraction := Verified.Expr.Alg.fractionResult expr
  let numerator ← Verified.Expr.Alg.mvPolyOf? fraction.num
  let denominator ← Verified.Expr.Alg.mvPolyOf? fraction.den
  let denominator := Verified.Expr.Alg.mvNormalize denominator
  if denominator.isEmpty then
    none
  else
    let (numerator, denominator) := lowestTerms numerator denominator
    let division :=
      Polynomial.Sparse.Univariate.divide numerator denominator
    let quotientExpr :=
      Verified.Expr.Alg.mvPolyExpr division.quotient
    let quotientPrimitive ←
      Polynomial.candidate? (0 : Fin 1) quotientExpr
    let properPrimitive ←
      Hermite.candidate? division.remainder denominator provider?
    some (Verified.Expr.simplifyAdd quotientPrimitive properPrimitive)

/--
The primitive of `x ^ k / denominator` from the prepared Hermite data of the denominator. It is
the candidate `candidate?` builds for that quotient, without decomposing the denominator again.
-/
def powerCandidateWith? (denominator : CAS.Polynomial.Sparse.Univariate)
    (prepared : Hermite.Prepared) (k : Nat) : Option (Verified.Expr (Fin 1)) := do
  let numerator ← Verified.Expr.Alg.mvPolyOf? (Verified.Expr.mkPow (.var (0 : Fin 1)) k)
  let division :=
    Polynomial.Sparse.Univariate.divide numerator denominator
  let quotientPrimitive ←
    Polynomial.candidate? (0 : Fin 1) (Verified.Expr.Alg.mvPolyExpr division.quotient)
  let properPrimitive ←
    if Polynomial.Sparse.isZero division.remainder then pure (0 : Verified.Expr (Fin 1))
    else Hermite.candidateWith? prepared division.remainder
  some (Verified.Expr.simplifyAdd quotientPrimitive properPrimitive)

/--
Integrate in any selected coordinate, with parameter-dependent numerator coefficients.

The denominator must have rational coefficients in that coordinate. Numerator terms may have
arbitrary coefficients independent of it, including transcendental expressions in parameters.
Each such coefficient is kept outside the univariate calculation. This extends the existing
rational reduction without treating another coordinate as the integration variable. The
denominator is decomposed once, and each power of the coordinate in the numerator is integrated
once.
-/
def rationalDenominatorCandidateIn? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n))
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (Verified.Expr (Fin n)) := do
  let lower := Verified.Expr.mapVars (fun _ : Fin n ↦ .var (0 : Fin 1))
  let restore := Verified.Expr.mapVars (fun _ : Fin 1 ↦ .var i)
  let independentCoordinates := (List.finRange n).filter (· != i)
  if independentCoordinates.all (fun j ↦ !Verified.Expr.containsVar j expr) then
    return restore (← candidate? (lower expr) provider?)
  let fraction := Verified.Expr.Alg.fractionResult expr
  guard (independentCoordinates.all (fun j ↦ !Verified.Expr.containsVar j fraction.den))
  let denominator :=
    Verified.Expr.Alg.mvNormalize (← Verified.Expr.Alg.mvPolyOf? (lower fraction.den))
  let prepared? := Hermite.prepare? denominator provider?
  let terms := Verified.Expr.Alg.normalizePoly (Verified.Expr.Alg.polyOf fraction.num)
  let mut primitives : List (Verified.Expr (Fin n)) := []
  let mut cache : List (Nat × Verified.Expr (Fin 1)) := []
  for term in terms do
    let (dependentFactors, coefficients) := term.2.partition (Verified.Expr.containsVar i)
    guard (dependentFactors.all (· == .var i))
    let coefficient := Verified.Expr.simplifyMul
      (Verified.Expr.mkRatConst term.1) (Verified.Expr.Alg.monoExpr coefficients)
    let k := dependentFactors.length
    let primitive ← match List.lookup k cache with
      | some primitive => pure primitive
      | none => prepared?.bind (powerCandidateWith? denominator · k)
    cache := (k, primitive) :: cache
    primitives := Verified.Expr.simplifyMul coefficient (restore primitive) :: primitives
  some (Verified.Expr.mkAddList primitives.reverse)

namespace Parameterized

open Verified.Expr

/-- Remove trailing coefficients that are syntactically zero. -/
def trimCoefficients {n : Nat} (coefficients : List (Verified.Expr (Fin n))) :
    List (Verified.Expr (Fin n)) :=
  (coefficients.reverse.dropWhile (· == .nat 0)).reverse

/-- Add coefficient arrays without expanding parameter expressions. -/
def addCoefficients {n : Nat} (p q : List (Verified.Expr (Fin n))) :
    List (Verified.Expr (Fin n)) :=
  trimCoefficients <| (List.range (max p.length q.length)).map fun k ↦
    simplifyAdd (p.getD k 0) (q.getD k 0)

/-- Convolve coefficient arrays when their product has degree at most sixteen. -/
def multiplyCoefficients? {n : Nat} (p q : List (Verified.Expr (Fin n))) :
    Option (List (Verified.Expr (Fin n))) := do
  guard (p.length + q.length ≤ 18)
  return trimCoefficients <| (List.range (p.length + q.length - 1)).map fun k ↦
    mkAddList <| (List.range p.length).map fun j ↦
      if j ≤ k then simplifyMul (p.getD j 0) (q.getD (k - j) 0) else 0

/-- Polynomial coefficients in the selected coordinate, retaining arbitrary independent
expressions as coefficients. The degree limit is sixteen; products are rejected before their
coefficient arrays exceed that limit. No parameter polynomial is expanded. -/
def coefficients? {n : Nat} (i : Fin n) (expr : Verified.Expr (Fin n)) :
    Option (List (Verified.Expr (Fin n))) :=
      if !containsVar i expr then some [simplify expr]
      else match expr with
        | .var j => if j = i then some [0, 1] else none
        | .add a b => do
            return addCoefficients (← coefficients? i a) (← coefficients? i b)
        | .sub a b => do
            return addCoefficients (← coefficients? i a) ((← coefficients? i b).map mkNeg)
        | .neg a => do return (← coefficients? i a).map mkNeg
        | .mul a b => do multiplyCoefficients? (← coefficients? i a) (← coefficients? i b)
        | .div a b => do
            guard (!containsVar i b)
            return trimCoefficients <| (← coefficients? i a).map (fun c ↦ simplifyDiv c b)
        | .pow a k => do
            guard (k ≤ 16)
            let base ← coefficients? i a
            (List.range k).foldlM (fun result _ ↦ multiplyCoefficients? result base) [1]
        | _ => none

/-- Reconstruct a polynomial in the selected coordinate from its coefficients. -/
def ofCoefficients {n : Nat} (i : Fin n)
    (coefficients : List (Verified.Expr (Fin n))) : Verified.Expr (Fin n) :=
  mkAddList <| coefficients.zipIdx |>.map fun (coefficient, k) ↦
    simplifyMul coefficient (mkPow (.var i) k)

/-- Integrate a coefficient array term by term in the selected coordinate. -/
def primitiveOfCoefficients {n : Nat} (i : Fin n)
    (coefficients : List (Verified.Expr (Fin n))) : Verified.Expr (Fin n) :=
  mkAddList <| coefficients.zipIdx |>.map fun (coefficient, k) ↦
    simplifyMul (simplifyDiv coefficient (.nat (k + 1))) (mkPow (.var i) (k + 1))

/-- Polynomial division with symbolic coefficients is only a proposal. Setting each leading
remainder coefficient to zero assumes the divisor's leading coefficient is nonzero; the final
antiderivative checker must prove that assumption and the complete differentiated identity. -/
def divideCoefficients {n : Nat} (numerator denominator : List (Verified.Expr (Fin n))) :
    List (Verified.Expr (Fin n)) × List (Verified.Expr (Fin n)) := Id.run do
  let degree := denominator.length - 1
  let mut remainder := numerator
  let mut quotient := List.replicate (numerator.length - degree) (0 : Verified.Expr (Fin n))
  for k in (List.range quotient.length).reverse do
    let coefficient := simplifyDiv (remainder.getD (degree + k) 0)
      (denominator.getD degree 0)
    quotient := quotient.set k coefficient
    remainder := remainder.set (degree + k) 0
    for j in [:degree] do
      remainder := remainder.set (j + k)
        (simplifySub (remainder.getD (j + k) 0)
          (simplifyMul coefficient (denominator.getD j 0)))
  return (trimCoefficients quotient, trimCoefficients remainder)

/-- Plan rational primitives with parameter-dependent linear or quadratic denominators.
Polynomial division handles numerator degree at most sixteen. Quadratics use the arctangent
branch with `4*a*c-b^2 > 0`; its positivity, the leading coefficient, and every remaining domain
condition are obligations of the existing checker. Degenerate and logarithmic quadratic
branches can be supplied through the explicit-primitive interface. -/
def candidate? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  let fraction := Verified.Expr.Alg.fractionResult expr
  let numerator ← coefficients? i fraction.num
  let denominator := trimCoefficients (← coefficients? i fraction.den)
  guard (1 < denominator.length && denominator.length ≤ 3)
  let (quotient, remainder) := divideCoefficients numerator denominator
  let denominatorExpr := ofCoefficients i denominator
  let proper ← if denominator.length = 2 then
      pure <| simplifyMul (simplifyDiv (remainder.getD 0 0) (denominator.getD 1 0))
        (mkLog denominatorExpr)
    else do
      let a := denominator.getD 2 0
      let b := denominator.getD 1 0
      let c := denominator.getD 0 0
      let alpha := simplifyDiv (remainder.getD 1 0) (simplifyMul 2 a)
      let beta := simplifySub (remainder.getD 0 0) (simplifyMul alpha b)
      let delta := simplifySub (simplifyMul 4 (simplifyMul a c)) (mkPow b 2)
      let scale := mkSqrt delta
      let affine := simplifyAdd (simplifyMul (simplifyMul 2 a) (.var i)) b
      pure <| simplifyAdd (simplifyMul alpha (mkLog denominatorExpr))
        (simplifyMul (simplifyDiv (simplifyMul 2 beta) scale)
          (.atan (simplifyDiv affine scale)))
  return simplifyAdd (primitiveOfCoefficients i quotient) proper

end Parameterized

/-- Prefer rational-coefficient Hermite reduction, then try bounded symbolic coefficient
reduction. Every proposal is checked by the caller against the original integrand. -/
def candidateIn? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n))
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (Verified.Expr (Fin n)) :=
  (rationalDenominatorCandidateIn? i expr provider?).orElse fun _ ↦
    Parameterized.candidate? i expr

/-- Whether the denominator of `expr`, a rational function of coordinate `i` with rational
coefficients, has a square-free factor that `split` without a factor provider leaves at degree
three or more (with `CASHex.Factor` imported, Hex's factorizer splits such a factor when it is
reducible over `ℚ`). A heuristic for the hint
of a failed integration: it looks at the written integrand only, so a rational function that a
substitution produces is not seen. -/
def needsFactorProvider {n : Nat} (i : Fin n) (expr : Verified.Expr (Fin n)) : Bool := Id.run do
  let fraction := Verified.Expr.Alg.fractionResult expr
  if (List.finRange n).any (fun j ↦ j != i && Verified.Expr.containsVar j fraction.den) then
    return false
  let lower := Verified.Expr.mapVars (fun _ : Fin n ↦ .var (0 : Fin 1))
  let some denominator := Verified.Expr.Alg.mvPolyOf? (lower fraction.den) | return false
  let denominator := Verified.Expr.Alg.mvNormalize denominator
  let some leading := Verified.Expr.Alg.mvLeadingTermNormalized? denominator | return false
  let some factors := Polynomial.Sparse.Univariate.squareFreeFactors?
      (Polynomial.Sparse.scale (1 / leading.1) denominator) | return false
  return factors.any fun factor ↦
    match Polynomial.Sparse.Univariate.RationalFactorization.split factor.factor with
    | some parts => parts.any (Polynomial.Sparse.Univariate.degree · ≥ 3)
    | none => false

end CAS.IntegrationPlanner.Rational
