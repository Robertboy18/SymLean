/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.UnivariateCalculus

/-!
# Exact sparse univariate division

Long division `divide` with its result `DivisionResult`, the scaling `monic` and the monic gcd
`gcd` of univariate sparse polynomials over `ℚ`, shared by symbolic integration, rational
canonicalization, rational factor splitting and real-root certification. They generate candidate
data, and the clients that state theorems check the polynomial identities they use.

## Implementation notes

`divide` normalizes both inputs and reduces the leading term of the remainder by a monomial multiple
of the divisor until the remainder's leading monomial is no longer divisible by the divisor's.
Over `ℚ` every step lowers the degree of the remainder, so the fuel `degree dividend + 1` suffices.
Since the inputs are canonical and every subtraction canonicalizes the next remainder, the loop
reads leading terms without normalizing again (`reduceLeadingNormalized?`, and `degree` with
`normalize := false`). `gcd` runs the Euclidean remainder loop `gcdAux` with fuel
`degree left + degree right + 2` and makes the last nonzero remainder monic.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse.Univariate

open CAS

/-- Quotient and remainder produced by sparse univariate long division. -/
structure DivisionResult where
  /-- Sparse quotient accumulated by the completed long-division steps. -/
  quotient : Sparse.Univariate
  /-- Residual polynomial left when the fuel-bounded division terminates. -/
  remainder : Sparse.Univariate
deriving DecidableEq

/-- Degree, with zero assigned to the zero polynomial for executable candidate generation.

The default normalizes the polynomial before reading its leading term. `normalize := false`
is for callers that already maintain canonical sparse order, such as the division loop. -/
def degree (polynomial : Sparse.Univariate) (normalize : Bool := true) : Nat :=
  let leading := if normalize then
    Verified.Expr.Alg.mvLeadingTermNormalized? polynomial
  else Verified.Expr.Alg.mvLeadingTerm? polynomial
  match leading with
  | none => 0
  | some term => term.2 (0 : Fin 1)

/--
Reduce canonical sparse polynomials without canonicalizing them again to find
their leading terms. The subtraction still canonicalizes the next remainder.
-/
def reduceLeadingNormalized?
    (dividend divisor : Sparse.Univariate) :
    Option (Rat × Verified.Expr.Alg.MvMonomial 1 × Sparse.Univariate) := do
  let dividendLead ← Verified.Expr.Alg.mvLeadingTerm? dividend
  let divisorLead ← Verified.Expr.Alg.mvLeadingTerm? divisor
  let quotientMono ←
    Verified.Expr.Alg.mvQuotient? divisorLead.2 dividendLead.2
  let quotientCoeff := dividendLead.1 / divisorLead.1
  let reduced :=
    Verified.Expr.Alg.mvSub dividend
      (Verified.Expr.Alg.mvScaleMonomial quotientCoeff quotientMono divisor)
  some (quotientCoeff, quotientMono, reduced)

/-- Fuel-bounded long-division loop for a canonical `divisor`.

Each step reduces the leading term of the current remainder and adds the resulting monomial
to the accumulated quotient. The loop stops when the fuel is exhausted or the leading term of
the remainder is not divisible by the leading term of `divisor`. -/
def divideAux (divisor : Sparse.Univariate) :
    Nat → Sparse.Univariate → Sparse.Univariate → DivisionResult
  | 0, quotient, remainder =>
      { quotient := quotient
        remainder := remainder }
  | fuel + 1, quotient, remainder =>
      match reduceLeadingNormalized? remainder divisor with
      | none =>
          { quotient := quotient
            remainder := remainder }
      | some (quotientCoeff, quotientMono, reduced) =>
          divideAux divisor fuel
            (Verified.Expr.Alg.mvAdd quotient
              [(quotientCoeff, quotientMono)])
            reduced

/--
Fuel-bounded exact sparse long division.

The result is candidate data. Callers that need the identity
`dividend = divisor * quotient + remainder` check it independently.
-/
def divide (dividend divisor : Sparse.Univariate) : DivisionResult :=
  let dividend := Verified.Expr.Alg.mvNormalize dividend
  let divisor := Verified.Expr.Alg.mvNormalize divisor
  divideAux divisor (degree dividend (normalize := false) + 1) [] dividend

/-- Scale a nonzero sparse polynomial to leading coefficient one. -/
def monic (polynomial : Sparse.Univariate) : Sparse.Univariate :=
  match Verified.Expr.Alg.mvLeadingTermNormalized? polynomial with
  | none => Sparse.zero
  | some lead =>
      Verified.Expr.Alg.mvScaleMonomial (1 / lead.1)
        (Verified.Expr.Alg.mvOne 1) polynomial

/-- Fuel-bounded Euclidean remainder loop for the gcd.

Each step replaces `(polynomial, divisor)` by `(divisor, polynomial mod divisor)`. The loop
returns the normalized `polynomial` when `divisor` normalizes to zero or the fuel runs out. -/
def gcdAux :
    Nat → Sparse.Univariate → Sparse.Univariate → Sparse.Univariate
  | 0, polynomial, _ => Verified.Expr.Alg.mvNormalize polynomial
  | fuel + 1, polynomial, divisor =>
      let divisor := Verified.Expr.Alg.mvNormalize divisor
      if divisor.isEmpty then
        Verified.Expr.Alg.mvNormalize polynomial
      else
        gcdAux fuel divisor (divide polynomial divisor).remainder

/-- Computable monic gcd candidate for two sparse univariate polynomials. -/
def gcd (left right : Sparse.Univariate) : Sparse.Univariate :=
  monic (gcdAux (degree left + degree right + 2) left right)

end CAS.Polynomial.Sparse.Univariate
