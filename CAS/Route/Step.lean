/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module


/-!
# Planner route steps

`RouteStep` names the transformations performed by the interval and CEGA planner. A route
step is diagnostic data only; soundness comes from the checked route or certificate.

## Implementation notes

Two types name steps in reports. `RouteStep` is the closed vocabulary of the interval and CEGA
planner (`Continuum/IntervalEval`, `Continuum/CompiledDerivative`, and the `#cas [enclose]`
reports in `Command/CEGA`): each constructor names one argument of the planner, such as an
enclosure rule or a monotonicity transfer, a route lists the steps the planner used to build it,
and the reports render a step by matching on its constructor. `CAS.Verified.Expr.PassInfo`
(`ClosedForm/Pipeline/Core`) is open metadata of the exact symbolic pipeline: the name,
proof-obligation class and phase of a configured pass. The `steps` field of a `SideClaimRoute`
lists the configured passes that built the claim, whether or not each one changed the
expression. We keep them as separate types because different layers read them (the numerical
planner and its command renderer, and the exact pipeline), and neither ever enters a proof.
-/

@[expose] public section

namespace CAS

/-- A transformation used while constructing a certified symbolic or interval route. -/
inductive RouteStep where
  /-- Normalize by exact symbolic equalities. -/
  | exactNormalization
  /-- Enclose an affine combination using rational arithmetic. -/
  | affineArithmetic
  /-- Combine checked child enclosures using a covering subdivision. -/
  | boxSubdivision
  /-- Use an increasing function to transfer endpoint bounds. -/
  | monotoneIncreasingRange
  /-- Use a decreasing function to transfer endpoint bounds. -/
  | monotoneDecreasingRange
  /-- Bound the deviation from a center using derivative enclosures. -/
  | centeredForm
  /-- Use the lower endpoint of a coordinate interval. -/
  | variableLowerBound
  /-- Combine factor bounds to obtain a product lower bound. -/
  | productLowerBound
  /-- Use nonnegativity or separation from zero to bound a square. -/
  | squareLowerBound
  /-- Use a checked natural-power lower bound. -/
  | powerLowerBound
  /-- Extract the lower endpoint of an interval enclosure. -/
  | intervalLowerBound
  /-- Use a checked square-root range. -/
  | sqrtRange
  /-- Use a checked arctangent range. -/
  | atanRange
  /-- Use a checked arcsine range. -/
  | asinRange
  /-- Use a checked arccosine range. -/
  | acosRange
  /-- Use a checked logarithm range. -/
  | logRange
  /-- Use a checked exponential range. -/
  | expRange
  /-- Use a checked hyperbolic-function range. -/
  | hyperbolicRange
  /-- Invert bounds on an interval separated from zero on the positive side. -/
  | reciprocalPositiveRange
  /-- Invert bounds on an interval separated from zero on the negative side. -/
  | reciprocalNegativeRange
deriving Repr, DecidableEq

end CAS
