/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Rat.Sqrt
public import CAS.ClosedForm.Expression.Rational.Proportionality
public import CAS.Integration.Elementary
public import CAS.Polynomial.Sparse
public import CAS.Polynomial.Sparse.Division

/-!
# Elementary square-free rational primitives

Primitives of the proper rational fractions left after polynomial and Hermite
reduction, over a square-free denominator. `candidate?` tries in turn a logarithmic derivative
(a numerator that is a constant multiple of the derivative of the denominator), a linear
numerator over a quadratic (`quadraticCandidate?`), a monic reciprocal quartic
`x^4 + a*x^2 + 1` for `-2 < a < 2` (`reciprocalQuarticCandidate?`), and the elementary table
`Elementary.candidate?`. Completed-square scales use exact rational constants when possible
(`exactSqrt?`) and symbolic square roots of rationals otherwise (`positiveSqrtExpr`).

## Implementation notes

The formulas are the classical ones of calculus. Completing the square, `quadraticCandidate?`
writes the primitive of `(p*x + q) / (a*x^2 + b*x + c)` as `p / (2*a)` times the logarithm of
the denominator, plus an arctangent when `4*a*c - b^2 > 0` or the logarithm of a quotient of
two affine terms when `4*a*c - b^2 < 0`. The quartic is the product of the positive-definite
quadratics `x^2 + s*x + 1` and `x^2 - s*x + 1` with `s^2 = 2 - a`, so its proper fraction is
split into two such quadratic fractions (`linearOverPositiveQuadraticPrimitive`). Hermite's
`prepare?` splits higher-degree factors with the rational factorization pass beforehand; the
logarithmic part is not computed by resultants (Rothstein-Trager or Lazard-Rioboo-Trager), so
an irreducible factor of degree three or more is handled only when it is one of these quartics
or the numerator is a constant multiple of its derivative.

No identity here is proved. `integrate?` accepts a primitive through
`IntegrationCheck.certifyCandidate?` only when the checked route `IntegrationCheck.route`
reduces its derivative residual to literal zero. The positivity of the square-root arguments
and the nonvanishing of denominators and logarithm arguments are then requirements of the
certificate (`IntegrationCheck.AntiderivativeCert.requirements`), under which
`IntegrationCheck.AntiderivativeCert.eval_diff_eq` gives the derivative identity.

## References

* Manuel Bronstein, *Symbolic Integration I: Transcendental Functions*, 2nd ed., Springer,
  Berlin, 2005, <https://doi.org/10.1007/b138171>. Chapter 2, Integration of Rational
  Functions, pp. 35-73.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.RationalElementary

open CAS.Polynomial

/-- Return Mathlib's nonnegative rational square root exactly when it squares back to `q`. -/
def exactSqrt? (q : Rat) : Option Rat :=
  if IsSquare q then some (Rat.sqrt q) else none

/-- Exact symbolic representation of the positive square root of a rational. -/
def positiveSqrtExpr (q : Rat) : Verified.Expr (Fin 1) :=
  match exactSqrt? q with
  | some root => Verified.Expr.mkRatConst root
  | none => Verified.Expr.mkSqrt (Verified.Expr.mkRatConst q)

/--
Integrate a proper linear-over-quadratic fraction when completing the square
produces either an arctangent or a real logarithmic branch.
-/
def quadraticCandidate? (remainder denominator : Sparse.Univariate) :
    Option (Verified.Expr (Fin 1)) := do
  if Sparse.Univariate.degree remainder > 1 ||
      Sparse.Univariate.degree denominator > 2 then
    none
  let denominatorQuadratic := Sparse.coefficient 2 denominator
  if denominatorQuadratic = 0 then
    none
  let denominatorLinear := Sparse.coefficient 1 denominator
  let denominatorConstant := Sparse.coefficient 0 denominator
  let numeratorLinear := Sparse.coefficient 1 remainder
  let numeratorConstant := Sparse.coefficient 0 remainder
  let alpha := numeratorLinear / (2 * denominatorQuadratic)
  let beta := numeratorConstant - alpha * denominatorLinear
  let delta :=
    4 * denominatorQuadratic * denominatorConstant -
      denominatorLinear * denominatorLinear
  if delta = 0 then
    none
  else
    let x : Verified.Expr (Fin 1) := .var 0
    let denominatorExpr := Verified.Expr.Alg.mvPolyExpr denominator
    let affine :=
      Verified.Expr.simplifyAdd
        (Verified.Expr.simplifyMul
          (Verified.Expr.mkRatConst (2 * denominatorQuadratic)) x)
        (Verified.Expr.mkRatConst denominatorLinear)
    let logarithmic :=
      Verified.Expr.simplifyMul
        (Verified.Expr.mkRatConst alpha)
        (Verified.Expr.mkLog denominatorExpr)
    let residualPrimitive :=
      if 0 < delta then
        let scale := positiveSqrtExpr delta
        let phase := Verified.Expr.simplifyDiv affine scale
        Verified.Expr.simplifyMul
          (Verified.Expr.simplifyDiv
            (Verified.Expr.mkRatConst (2 * beta)) scale)
          (.atan phase)
      else
        let scale := positiveSqrtExpr (-delta)
        let ratio :=
          Verified.Expr.simplifyDiv
            (Verified.Expr.simplifySub affine scale)
            (Verified.Expr.simplifyAdd affine scale)
        Verified.Expr.simplifyMul
          (Verified.Expr.mkRatConst beta)
          (Verified.Expr.simplifyDiv
            (Verified.Expr.mkLog ratio) scale)
    some (Verified.Expr.simplifyAdd logarithmic residualPrimitive)

/--
Candidate primitive of `(linear * x + constant) / (x^2 + shift * x + 1)`, where `scale` stands
for the positive square root of `4 - shift^2`. The result is
`alpha * log(x^2 + shift * x + 1) + (2 * beta / scale) * atan((2 * x + shift) / scale)` with
`alpha = linear / 2` and `beta = constant - alpha * shift`; no identity is proved here.
-/
def linearOverPositiveQuadraticPrimitive
    (linear constant shift scale : Verified.Expr (Fin 1)) :
    Verified.Expr (Fin 1) :=
  let x : Verified.Expr (Fin 1) := .var 0
  let two := Verified.Expr.mkRatConst 2
  let quadratic :=
    Verified.Expr.simplifyAdd
      (Verified.Expr.simplifyAdd (x ^ 2)
        (Verified.Expr.simplifyMul shift x))
      1
  let alpha := Verified.Expr.simplifyDiv linear two
  let beta :=
    Verified.Expr.simplifySub constant
      (Verified.Expr.simplifyMul alpha shift)
  let logarithmic :=
    Verified.Expr.simplifyMul alpha (Verified.Expr.mkLog quadratic)
  let phase :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.simplifyAdd
        (Verified.Expr.simplifyMul two x) shift)
      scale
  let arctangent :=
    Verified.Expr.simplifyMul
      (Verified.Expr.simplifyDiv
        (Verified.Expr.simplifyMul two beta) scale)
      (.atan phase)
  Verified.Expr.simplifyAdd logarithmic arctangent

/--
Candidate for a proper fraction over `x^4 + a*x^2 + 1`, with `-2 < a < 2`.

With `s^2 = 2 - a` and `t^2 = 2 + a`, the intended algebra is

`x^4 + a*x^2 + 1 = (x^2 + s*x + 1) * (x^2 - s*x + 1)`

and `4 - s^2 = t^2`. The strict bounds on `a` make `s` and `t` positive and
the two quadratic factors positive-definite. This planner constructs the
candidate but proves none of these identities. The integration checker
differentiates the candidate, normalizes the residual, and records the
required positivity and nonzero-domain obligations.
-/
def reciprocalQuarticCandidate?
    (remainder denominator : Sparse.Univariate) :
    Option (Verified.Expr (Fin 1)) := do
  if Sparse.Univariate.degree remainder > 3 ||
      Sparse.Univariate.degree denominator > 4 then
    none
  let a := Sparse.coefficient 2 denominator
  if Sparse.coefficient 4 denominator ≠ 1 ||
      Sparse.coefficient 3 denominator ≠ 0 ||
      Sparse.coefficient 1 denominator ≠ 0 ||
      Sparse.coefficient 0 denominator ≠ 1 then
    none
  if ¬ ((-2 : Rat) < a ∧ a < 2) then
    none
  let r0 := Sparse.coefficient 0 remainder
  let r1 := Sparse.coefficient 1 remainder
  let r2 := Sparse.coefficient 2 remainder
  let r3 := Sparse.coefficient 3 remainder
  let s := positiveSqrtExpr (2 - a)
  let t := positiveSqrtExpr (2 + a)
  let two := Verified.Expr.mkRatConst 2
  let r0Expr := Verified.Expr.mkRatConst r0
  let r3Expr := Verified.Expr.mkRatConst r3
  /-
  Split the numerator as

    (A*x + B) / (x^2 + s*x + 1) +
    (C*x + D) / (x^2 - s*x + 1).

  Equating the four coefficients gives the two differences below, followed
  by

    A = (r3 - evenDifference) / 2,
    C = (r3 + evenDifference) / 2,
    B = (r0 - oddDifference) / 2,
    D = (r0 + oddDifference) / 2.

  These are candidate formulas; only the final differentiated residual is
  checked.
  -/
  let evenDifference :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.mkRatConst (r2 - r0)) s
  let oddDifference :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.mkRatConst (r1 - r3)) s
  let plusLinear :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.simplifySub r3Expr evenDifference) two
  let minusLinear :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.simplifyAdd r3Expr evenDifference) two
  let plusConstant :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.simplifySub r0Expr oddDifference) two
  let minusConstant :=
    Verified.Expr.simplifyDiv
      (Verified.Expr.simplifyAdd r0Expr oddDifference) two
  some <| Verified.Expr.simplifyAdd
    (linearOverPositiveQuadraticPrimitive plusLinear plusConstant s t)
    (linearOverPositiveQuadraticPrimitive minusLinear minusConstant
      (Verified.Expr.mkNeg s) t)

/-- Candidate primitive for a proper fraction with square-free denominator. -/
def candidate? (remainder denominator : Sparse.Univariate) :
    Option (Verified.Expr (Fin 1)) :=
  if Sparse.isZero remainder then
    some 0
  else
    let remainderExpr := Verified.Expr.Alg.mvPolyExpr remainder
    let denominatorExpr := Verified.Expr.Alg.mvPolyExpr denominator
    let fraction := Verified.Expr.simplifyDiv remainderExpr denominatorExpr
    let logarithmic : Option (Verified.Expr (Fin 1)) := do
      let proportionality ←
        Verified.Expr.Alg.proportionality?
          remainderExpr (denominatorExpr.diff (0 : Fin 1))
      let factor := Verified.Expr.simplify proportionality.expr
      if Verified.Expr.containsVar (0 : Fin 1) factor then
        none
      else
        some (Verified.Expr.simplifyMul factor
          (Verified.Expr.mkLog denominatorExpr))
    match logarithmic with
    | some primitive => some primitive
    | none =>
        match quadraticCandidate? remainder denominator with
        | some primitive => some primitive
        | none =>
            match reciprocalQuarticCandidate? remainder denominator with
            | some primitive => some primitive
            | none =>
                Elementary.candidate? (0 : Fin 1) fraction

end CAS.IntegrationPlanner.RationalElementary
