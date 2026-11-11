/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.Interval.Elementary.Log
public import CAS.Continuum.Interval.Elementary.Sqrt

/-!
# Precision policy for certified evaluation

The automatic elementary-function ranges are parameterized by a Taylor order,
a number of series terms, or a number of binary digits, and checked box
refinement by a subdivision depth. `Precision` bundles those parameters so a
CEGA query can carry one user-selected policy through the registry planner.

Precision is planner data. Every range theorem is proved for all parameter
values, so the policy affects the sharpness and the cost of an enclosure but
never its soundness.

Only the exponential, hyperbolic, logarithm and square-root ranges and the
subdivision depth read the policy. The sine, cosine and inverse trigonometric
ranges and the `π` bracket of the rational evaluator keep fixed precisions, so a
larger policy need not sharpen them. A `digits` request makes box enclosures try
`DigitsEval.eval` first, whose precision covers those functions too.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/--
Numerical precision policy for automatic interval compilation.

The defaults use exponential Taylor order 8, square-root refinement with 12
binary digits, 10 logarithm series terms, and subdivision depth 2.
-/
structure Precision where
  /-- Taylor order for exponential and hyperbolic ranges; zero is promoted to one. -/
  expOrder : ℕ := defaultExpTaylorOrder
  /-- Binary digits for square-root brackets (`sqrtRangeInterval`). -/
  sqrtDigits : ℕ := defaultSqrtRefinementSteps
  /-- Series terms for logarithm ranges (`logRangeWith`). -/
  logTerms : ℕ := logSeriesTerms
  /-- Number of checked bisection levels used by subdivided enclosures. -/
  depth : ℕ := 2
  /-- Requested decimal digits. When set, box enclosures first try the precision-parametric
  evaluator `DigitsEval.eval` at the working precision `DigitsEval.precisionFor digits`. -/
  digits : Option ℕ := none
deriving Repr, DecidableEq

namespace Precision

/--
The policy that requests `prec` Taylor terms for `exp`, `prec` series terms for
`log`, and `prec` binary digits for square roots, keeping the subdivision depth.
-/
def withPrec (policy : Precision) (prec : ℕ) : Precision :=
  { policy with expOrder := prec, sqrtDigits := prec, logTerms := prec }

/-- The policy with a requested subdivision depth. -/
def withDepth (policy : Precision) (depth : ℕ) : Precision :=
  { policy with depth := depth }

end Precision

end RationalInterval
end CAS.Continuum
