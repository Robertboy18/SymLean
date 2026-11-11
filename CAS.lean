/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module -- shake: keep-all

public import CAS.CEGA
public import CAS.Command.Algebra.Apart
public import CAS.Command.Algebra.Collect
public import CAS.Command.Algebra.PolynomialAlgebra
public import CAS.Command.AsymptoticLimits
public import CAS.Command.BesselJ
public import CAS.Command.Calls
public import CAS.Command.CEGA
public import CAS.Command.ComplexRoots
public import CAS.Command.Differential
public import CAS.Command.Digits
public import CAS.Command.DSolve
public import CAS.Command.DSolveOrder
public import CAS.Command.DSolveParam
public import CAS.Command.DSolveRoot
public import CAS.Command.FindRoot
public import CAS.Command.FullSimplify
public import CAS.Command.InfiniteSum
public import CAS.Command.Gamma
public import CAS.Command.Goals
public import CAS.Command.FourierProduct
public import CAS.Command.FourierTransform
public import CAS.Command.Ideal
public import CAS.Command.Integration
public import CAS.Command.IntervalExtrema
public import CAS.Command.Laplace
public import CAS.Command.Laurent
public import CAS.Command.LinearAlgebra.Eigen
public import CAS.Command.LinearAlgebra.Operations
public import CAS.Command.Limits
public import CAS.Command.Matrix
public import CAS.Command.Minimize
public import CAS.Command.NIntegrate
public import CAS.Command.NIntegrateSingular
public import CAS.Command.NumberTheory.Functions
public import CAS.Command.OrthogonalPolynomials
public import CAS.Command.ParamSystems
public import CAS.Command.PolySystems
public import CAS.Command.Product
public import CAS.Command.RSolve
public import CAS.Command.Reduce
public import CAS.Command.Roots
public import CAS.Command.RootSplit
public import CAS.Command.Series
public import CAS.Command.Simplification
public import CAS.Command.Solving
public import CAS.Command.SpecialFunctions
public import CAS.Command.Sum
public import CAS.Command.SumGosper
public import CAS.Command.Systems
public import CAS.Command.Zeta
public import CAS.Command.Erf
public import CAS.Command.GaussianIntegral
public import CAS.Command.InverseLaplace
public import CAS.Command.NDSolve
public import CAS.Command.UnknownMode
public import CAS.ExactTactic
public import CAS.IntegrationTactic
public import CAS.Reporting
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Checked computer algebra system and CEGA

`CAS` is the single import for the checked calculator: the theorem
tactics, the finite-box certificates, the `#cas` commands, and the optional
reports. Bare `cega` includes automatic certified quadrature. Further
quadrature APIs, validated linear algebra, ODE enclosures, and polynomial roots
live in the modules under `CAS/Continuum` and `CAS/Polynomial`.
Library modules should import the narrowest module that defines what they use.

## Commands and tactics

The `#cas` command prints a checked calculation on an expression written in a
restricted real-scalar syntax, without closing a goal:

```lean
#cas [derive x] (2 * x) -- 2
#cas [derive] (fun x : ℝ ↦ a * x + b) -- a
#cas [simplify] ((x + 0) * 1)
#cas [fullSimplify] (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)
#cas [factor] (x ^ 3 - x)
#cas [derive x] (sin (x * y))
#cas [grad x, y] (sin (x * y))
#cas [integrate x] (x * sin (x ^ 2))
#cas [integrate x] (sin x ^ 2 * cos x ^ 2)
#cas [integrate] (fun x : ℝ ↦ 2) -- 2*x
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)
#cas [nintegrate x in [0, 1]] (exp (-x^2))
#cas [nintegrate x in [0, 1]] (sqrt x * exp x)
#cas [enclose] (sqrt 2)
#cas [N 50] (pi)
#cas (LegendreP 5 x)
#cas [solve x] (x ^ 2 = 1)
#cas [reduce x] (-2 * x + 3 ≤ 7)
#cas [reduce x] (x^3 - x ≥ 0)
#cas [solve x, y] (2*x + y = 1 ∧ x - y = 2)
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)
#cas [solve x, y] (a*x + y = 1 ∧ x + a*y = 1)
#cas [groebner x, y] [x^2 + y^2 - 5, x*y - 2]
#cas [member x, y] (x^2 - 1) [x*y - 1, x - y]
#cas [roots x] (x ^ 5 - x - 1 = 0)
#cas [roots z in ℂ] (z ^ 4 + 1 = 0)
#cas [series x 0 6] (exp (sin x))
#cas [series x 0 3] (1 / sin x)
#cas [limit x → 0] (sin x / x)
#cas [sum k 1 n] (k^2)
#cas [sum k 1 n] (1 / (k * (k + 1)))
#cas [limit x → ∞] ((x^2 + 1) / (2*x^2 - 3))
#cas [limit x → ∞] (x^2 * exp (-x))
#cas [limit x → 0 from above] (1 / x)
#cas [dsolve y x] (y'' + 3 * y' + 2 * y = exp x)
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)
#cas [dsolve y x] (y''' - y = 0)
#cas [dsolve y x] (y' + 2*x*y = x)
#cas [dsolve y x] (y' + a * y = sin (n * x))
#cas [dsolve y x] (y'''' + y = 0)
#cas [integrate x] (exp (a * x) * sin (n * x))
#cas [fourier x n] (x^2)
#cas [fourier x n] (x * sin x)
#cas [fourierSin x n pi] (x * (pi - x))
#cas [positiveDefinite] !![2, 1; 1, 2]
#cas [eigenvalueBounds] !![2, 1; 1, 2]
```

No prior variable declarations are needed. Write multiplication with `*`.
Use `#cas` directly; `#eval` evaluates executable Lean terms and is not part of
the calculator syntax. For `derive` and `integrate`, a unary lambda selects its
parameter, including for constant bodies. Other names in the body remain symbolic
parameters. A named coordinate must agree with the lambda binder.

The command reifies its input itself, so calculator users never construct
`Verified.Expr`, and it validates its report by adding auxiliary theorems for the
kernel to check. To state a result as a named theorem, use the theorem tactics on
ordinary Lean and Mathlib statements:

```lean
example (x : ℝ) :
    deriv Real.sin x = Real.cos x := by
  cas

example (ε x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2 + ε ^ 2) (2 * x) x := by
  cas

example (a b : ℝ) :
    (∫ t in a..b, Real.sin t) = Real.cos a - Real.cos b := by
  cas
```

`cas` proves `deriv`, `iteratedDeriv` and `iteratedDerivWithin` of a literal order,
`HasDerivAt`, `HasDerivWithinAt`, and `DifferentiableAt` statements about functions
`ℝ → ℝ` (nested derivatives included). Mathlib theorem rules and registered
`@[cas_deriv]` rules also handle scalar functions outside the reflected grammar,
including complex exponential and trigonometric functions. It proves the regularity
statements `Differentiable`, `DifferentiableOn`, `ContDiffAt`, `ContDiffOn`, `ContDiff`,
`ContinuousAt`, `ContinuousOn`, `Continuous`, `AnalyticAt` and `AnalyticOnNhd` and,
with this import, limits at a rational point and at `atTop` and `atBot`, interval
integrals and inequalities on rational boxes. Derivative backends for functions
`ℝ^n → ℝ` register themselves through `CAS.Tactic.DerivativeRegistry`.

`cas_nf` performs checked normalization inside a larger
proof. `cega` closes bounds, enclosures and approximations on rational boxes, either
by projecting a checked certificate or by running a box query
(`CAS.CEGA`). Bare `cega` also bounds an interval integral with a
closed real integrand and rational limits. The `using` forms of each tactic take explicit evidence.
`cas?` and `cega?` close the goal as the plain tactics would, then suggest the
call to keep, an explicit call when it closes the original goal and otherwise the
plain call, and attach a report. Unsupported targets fail without
changing the goal.

## What is proved

Search procedures and planner metadata prove nothing. Every accepted result
comes from a Lean theorem or a certificate soundness field, and reports mark
the remaining metadata as such. The `#cas` calculator works with real scalars.
Interval modes use finite-dimensional boxes with exact rational endpoints.
The reflected `Verified.Expr` API lives in the modules under `CAS/Expr`, `CAS/ClosedForm` and
`CAS/Exact`.
The manual, the website built from `Site/`, gives the full syntax, the public imports, and
the supported integration fragment.
-/
