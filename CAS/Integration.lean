/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Integration.Check
public import CAS.Integration.Planner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Checked symbolic antiderivatives

`integrate? i expr` is the one integration entry point for `Verified.Expr (Fin n)`. It returns an
`IntegrationCheck.AntiderivativeCert`, whose checked residual route reaches literal zero, or
`none`, never an unchecked guess. The analytic coordinate-line semantics of the certificate live
in `CAS/Calculus/Antiderivative.lean`.

## Implementation notes

`IntegrationPlanner.candidate?` (`CAS/Integration/Planner.lean`) proposes a primitive, and
`IntegrationCheck.certifyCandidate?` (`CAS/Integration/Check.lean`) accepts its simplified form
exactly when the residual route `IntegrationCheck.route` ends in `0`, so no proof depends on the
planner. The planner's module doc lists its methods. Besides polynomial, substitution, rational
(Euclidean division and Hermite reduction, `CAS/Integration/Rational.lean` and
`CAS/Integration/Hermite.lean`) and fuel-bounded integration-by-parts routes, it solves the
finite coupled recurrence for polynomial amplitudes multiplying common exponential and
sine/cosine phases, whose slopes may be symbolic as long as they are free of the integration
coordinate. An integrand in one trigonometric phase goes to `CAS/Integration/Bioche.lean`: a
polynomial in the sine and cosine over a denominator free of both is integrated monomial by
monomial, and a rational function of them becomes a rational integrand under `t = cos u`,
`t = sin u` or `t = tan u` when it has the matching symmetry. Substitution recursively reuses
these methods, and the half-angle substitution reduces the other rational expressions in a common
trigonometric phase to rational integration. Parameters in numerator coefficients are retained.
The optional factor provider factors denominators over `ℚ` for the rational route; the integrate
command passes the one of the route registry, which `CASHex.Factor` registers.
-/

@[expose] public section

namespace CAS

/-- Try to construct a checked symbolic antiderivative certificate in coordinate `i`. -/
def integrate? {n : Nat} (i : Fin n) (expr : Verified.Expr (Fin n))
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (IntegrationCheck.AntiderivativeCert i expr) := do
  let candidate ← IntegrationPlanner.candidate? i expr provider?
  IntegrationCheck.certifyCandidate? i expr candidate.simplify

end CAS
