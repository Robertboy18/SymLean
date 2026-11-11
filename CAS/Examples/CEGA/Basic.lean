/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS.CEGA

/-!
# The `cega` tactic on certificate goals

CEGA (Certified Enclosures, Guarantees, and Approximations) synthesizes checked interval
certificates for ordinary Lean goals. Functions and domains are stated in Lean and Mathlib
notation; the reflected expressions and the planner state stay inside the tactic.

The examples bound rational and transcendental functions on intervals and boxes,
convert an enclosure into a residual bound, and certify uniform approximation.
Subdivision handles turning points; centered mean-value bounds reduce the overestimation
caused by repeated variables. Further examples use trigonometric argument reduction and
coordinatewise monotonicity in two and three dimensions. Integral bounds, certificate goals and
conjunctions proved by bare `cega`, and the precision options have their own example modules:
`GaussianIntegral`, `NonsmoothIntegrals`, `BareGoals` and `Precision`.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Basic

open CAS.Certificate
open CAS.CEGA

/-! ## Function bounds -/

/-- The interval `[0, 1]`, represented as a one-coordinate box. -/
def unitDomain : Set (ℝ^1) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1}

/-- The interval `[1, 2]`, on which reciprocals and logarithms have positive arguments. -/
def positiveDomain : Set (ℝ^1) :=
  {p | 1 ≤ p 0 ∧ p 0 ≤ 2}

/-- The interval `[-1, 1]`, used to check enclosures across a change of sign. -/
def symmetricDomain : Set (ℝ^1) :=
  {p | -1 ≤ p 0 ∧ p 0 ≤ 1}

/-- The interval `[-2, 2]`, containing both critical points of `x / (1 + x²)`. -/
def criticalDomain : Set (ℝ^1) :=
  {p | -2 ≤ p 0 ∧ p 0 ≤ 2}

/-- The rectangle `[0, 1] × [2, 3]` for independent-coordinate product bounds. -/
def productDomain : Set (ℝ^2) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3}

/-- The positive square `[1, 2]²`. -/
def squareDomain : Set (ℝ^2) :=
  {p | 1 ≤ p 0 ∧ p 0 ≤ 2 ∧ 1 ≤ p 1 ∧ p 1 ≤ 2}

/-- The square `[9/10, 11/10]²` around `(1, 1)`. -/
def nearOneSquare : Set (ℝ^2) :=
  {p | 9 / 10 ≤ p 0 ∧ p 0 ≤ 11 / 10 ∧ 9 / 10 ≤ p 1 ∧ p 1 ≤ 11 / 10}

/-- The positive cube `[1, 2]³`. -/
def cubeDomain : Set (ℝ^3) :=
  {p | 1 ≤ p 0 ∧ p 0 ≤ 2 ∧ 1 ≤ p 1 ∧ p 1 ≤ 2 ∧ 1 ≤ p 2 ∧ p 2 ≤ 2}

/-- The residual `r(x) = x` has magnitude at most one on `[0, 1]`.
-/
example :
    ResidualBound (fun p : ℝ^1 ↦ p 0) unitDomain 1 := by
  apply enclosedOn_residualBound (lo := 0) (hi := 1)
  · cega [enclose x in [0, 1]] x
  · norm_num
  · norm_num

/-- A derivative-sign certificate gives the sharp endpoint range. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      unitDomain (0 : ℝ) (1 / 2 : ℝ) := by
  cega [enclose x in [0, 1]] (x / (1 + x))

/--
Subdivision exposes the turning points of `x / (1 + x²)` at `±1`.
Monotonicity on the resulting intervals certifies the sharp range.
-/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2))
      criticalDomain (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  cega (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/-- The same subdivision gives the upper bound that the sharp range implies. The planner's range
of `x / (1 + x²)` on the whole of `[-2, 2]` is `[-2, 2]`, which gives none of the bounds below. -/
example :
    BoundOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) criticalDomain (1 / 2 : ℝ) := by
  cega (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/-- The bound on the absolute value after the same subdivision. -/
example :
    BoundOn (fun p : ℝ^1 ↦ |p 0 / (1 + p 0 ^ 2)|) criticalDomain (1 / 2 : ℝ) := by
  cega (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/-- The approximation by the midpoint `0` of the sharp range, with its radius `1/2`. -/
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) (fun _ ↦ (0 : ℝ))
      criticalDomain (1 / 2 : ℝ) := by
  cega (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/-- Literal negative powers are certified through reciprocal power ranges. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 ^ (-2 : ℤ))
      positiveDomain (1 / 4 : ℝ) (1 : ℝ) := by
  cega [enclose x in [1, 2]] (x ^ (-2))

/-- One-sided range queries prove ordinary upper-bound propositions. -/
example :
    BoundOn (fun p : ℝ^1 ↦ p 0 - 2)
      unitDomain (0 : ℝ) := by
  cega [enclose x in [0, 1]] (x - 2)

/-- Absolute-bound queries certify magnitudes. -/
example :
    BoundOn (fun p : ℝ^1 ↦ |p 0 - 2|)
      unitDomain (3 : ℝ) := by
  cega [enclose x in [0, 1]] (x - 2)

/-- Approximation queries prove a uniform error budget for a concrete model. -/
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0) (fun _ ↦ (1 / 2 : ℝ))
      unitDomain (1 : ℝ) := by
  cega [enclose x in [0, 1]] x

/-- Queries may bind several coordinates in one finite-dimensional box. -/
example :
    EnclosedOn (fun p : ℝ^2 ↦ p 0 * p 1)
      productDomain (0 : ℝ) (3 : ℝ) := by
  cega [enclose x in [0, 1], y in [2, 3]] (x * y)

/-- Branch normalization uses positivity of the certified input panel. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.exp (Real.log (p 0)))
      positiveDomain (1 : ℝ) (2 : ℝ) := by
  cega [enclose x in [1, 2]] (exp (log x))

/-- Absolute-value lowering remains sharp on a box that crosses zero. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ |p 0|)
      symmetricDomain (0 : ℝ) (1 : ℝ) := by
  cega [enclose x in [-1, 1]] (|x|)

/-! ## Argument reduction for sine and cosine

FloatLib reduces arguments by full periods and combines point enclosures with
midpoint Lipschitz bounds. A certified derivative sign allows endpoint refinement
on monotone panels. The two examples below retain narrow rational targets far
from the origin, where the global range `[-1, 1]` is too wide. -/

/-- A narrow negative sine range on `[10, 10.01]`. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.sin (p 0))
      {p : ℝ^1 | 10 ≤ p 0 ∧ p 0 ≤ 1001 / 100} (-553 / 1000 : ℝ) (-543 / 1000 : ℝ) := by
  cega [enclose x in [10, 1001 / 100]] (sin x)

/-- A narrow positive cosine range on `[100, 100.001]`. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.cos (p 0))
      {p : ℝ^1 | 100 ≤ p 0 ∧ p 0 ≤ 100001 / 1000} (8623 / 10000 : ℝ) (8629 / 10000 : ℝ) := by
  cega [enclose x in [100, 100001 / 1000]] (cos x)

/-! ## Centered mean-value form

For `x · exp (-x)` on `[0.9, 1.1]` the natural interval extension gives
`[0.2996, 0.4473]`, and the derivative `exp (-x) · (1 - x)` changes sign, so the
monotonicity route does not apply. The centered form
`f(m) + f'(I) · (I - m)` certifies `[0.3563, 0.3794]`, six times narrower; the
true range is `[0.3659, 0.3679]`. -/

/-- The planner selects the centered form when it previews sharpest. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 * Real.exp (-p 0))
      {p : ℝ^1 | 9 / 10 ≤ p 0 ∧ p 0 ≤ 11 / 10} (7 / 20 : ℝ) (19 / 50 : ℝ) := by
  cega [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))

/-! ## Derivative routes on boxes of higher dimension

The monotonicity and centered-form routes apply to boxes of any literal
dimension. When a partial derivative keeps one sign on the box, the range is
attained on the two faces of that coordinate; each face reruns the planner, so
reductions can nest while further sign certificates and fuel are available. When no
partial derivative keeps one sign, the multivariate centered form
`f(m) + Σᵢ ∂ᵢf(B) · (Bᵢ - mᵢ)` competes with the natural extension. The
certified ranges before and after these routes:

| Expression | Box | Before | After |
|---|---|---|---|
| `x * y - x` | `[1, 2]²` | `[-1/2, 2]` | `[0, 2]` |
| `x * y * exp (-(x * y))` | `[0.9, 1.1]²` | `[0.2415, 0.5383]` | `[0.3030, 0.4327]` |
| `x * y * z - x * y` | `[1, 2]³` | `[-9/4, 9/2]` | `[0, 4]` |

All but the second result are the exact ranges; the true range of the second is
`[0.3604, 0.3679]`.
-/

/--
For `x * y - x` on `[1, 2]²`, the affine enclosure is `[-1/2, 2]`.
The partial derivative `y - 1` is nonnegative, so the box reduces to the faces
`x = 1` and `x = 2`, on which the remaining partial derivative keeps one sign;
the certified range `[0, 2]` is exact.
-/
example :
    EnclosedOn (fun p : ℝ^2 ↦ p 0 * p 1 - p 0)
      squareDomain (0 : ℝ) (2 : ℝ) := by
  cega [enclose x in [1, 2], y in [1, 2]] (x * y - x)

/--
Both partial derivatives of `x * y * exp (-(x * y))` change sign on
`[0.9, 1.1]²`, so no face reduction applies. The natural extension gives
`[0.241538, 0.538280]`; the multivariate centered form certifies
`[0.303083, 0.432632]`, less than half as wide. The true range is
`[0.3604, 0.3679]`.
-/
example :
    EnclosedOn (fun p : ℝ^2 ↦ p 0 * p 1 * Real.exp (-(p 0 * p 1)))
      nearOneSquare (3 / 10 : ℝ) (11 / 25 : ℝ) := by
  cega [enclose x in [9 / 10, 11 / 10], y in [9 / 10, 11 / 10]] (x * y * exp (-(x * y)))

/--
Three nested face reductions certify the exact range of `x * y * z - x * y` on
`[1, 2]³`, where the natural extension gives `[-9/4, 9/2]`.
-/
example :
    EnclosedOn (fun p : ℝ^3 ↦ p 0 * p 1 * p 2 - p 0 * p 1)
      cubeDomain (0 : ℝ) (4 : ℝ) := by
  cega [enclose x in [1, 2], y in [1, 2], z in [1, 2]] (x * y * z - x * y)

end CAS.Examples.CEGA.Basic
