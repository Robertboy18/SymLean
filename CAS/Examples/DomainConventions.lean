/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Domain conventions for symbolic calculation

Division, logarithms, square roots, and inverse trigonometric functions use
Mathlib's total real functions. These examples distinguish their values at
singular points from the hypotheses needed for differentiation and for the
logarithm identities. We also enclose their values on negative intervals and
intervals crossing zero.
-/

@[expose] public section

namespace CAS.Examples.DomainConventions

open CAS.Certificate

/-- The interval `[-1, 1]`, including the singular point of reciprocal expressions. -/
def crossingZeroDomain : Set (ℝ^1) :=
  {p | -1 ≤ p 0 ∧ p 0 ≤ 1}

/-- The interval `[-2, -1]`, bounded away from zero on the negative real axis. -/
def negativeDomain : Set (ℝ^1) :=
  {p | -2 ≤ p 0 ∧ p 0 ≤ -1}

/-- Positivity of `1 + x²` discharges the square-root substitution conditions. -/
example (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  cas

/-- A nested logarithm exposes both nonvanishing conditions explicitly. -/
example (x : ℝ) (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ Real.log (Real.log t))
      (1 / (x * Real.log x)) x := by
  cas

/-- A stated primitive with a repeated irreducible quadratic denominator is checked by
differentiation. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ t / (2 * (t ^ 2 + 1)) + Real.arctan t / 2)
      (1 / (x ^ 2 + 1) ^ 2) x := by
  cas

/-- Mathlib's total square root has range `[0,1]` on `[-1,1]`. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.sqrt (p 0))
      crossingZeroDomain (0 : ℝ) (1 : ℝ) := by
  cega [enclose x in [-1, 1]] (sqrt x)

/-- Mathlib's real logarithm is even, so its values on `[-2,-1]` are nonnegative. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.log (p 0))
      negativeDomain (0 : ℝ) (5057 / 7290 : ℝ) := by
  cega [enclose x in [-2, -1]] (log x)

/-- The total logarithm at zero is exact, unlike its unbounded values near zero. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.log (p 0))
      {p : ℝ^1 | p 0 = 0} 0 0 := by
  cega [enclose x in [0, 0]] (log x)

/-- Absolute values are lowered to square roots, so wide boxes stay exact as well. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ |p 0|)
      {p : ℝ^1 | -20 ≤ p 0 ∧ p 0 ≤ 1} (0 : ℝ) (20 : ℝ) := by
  cega [enclose x in [-20, 1]] (|x|)

/-- The constant right tail of the total arccosine includes its endpoint. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.arccos (p 0))
      {p : ℝ^1 | 1 ≤ p 0 ∧ p 0 ≤ 2} 0 0 := by
  cega [enclose x in [1, 2]] (acos x)

/-- Reciprocal bounds on a negative panel reverse the input endpoints. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ 1 / p 0) negativeDomain (-1) (-1 / 2) := by
  cega [enclose x in [-2, -1]] (1 / x)

/-! ## Side-condition discharge

The hypotheses supply the domain conditions needed by the calculation.
A nonzero scale makes a shifted quadratic radicand positive. Logarithmic
derivatives and identities retain the nonvanishing conditions on their arguments.
-/

/-- A shifted radicand `(x - a) ^ 2 + ε ^ 2` is positive as soon as the scale is nonzero. -/
example {a ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sqrt ((t - a) ^ 2 + ε ^ 2))
      ((x - a) / Real.sqrt ((x - a) ^ 2 + ε ^ 2)) x := by
  cas

-- Regression: with a literal scale the residual denominator arrives expanded, and its nonvanishing
-- must still be proved without a hypothesis.
/-- A literal scale needs no hypothesis, although the residual denominator arrives expanded. -/
example (c x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sqrt ((t - c / 2) ^ 2 + 1 ^ 2))
      ((x - c / 2) / Real.sqrt ((x - c / 2) ^ 2 + 1 ^ 2)) x := by
  cas

/-- Positivity evidence discharges the nonvanishing condition `4 * π * s ≠ 0`. -/
example (s : ℝ) (h : 0 < 4 * Real.pi * s) :
    deriv (fun t : ℝ ↦ Real.log (4 * Real.pi * t)) s = 1 / s := by
  cas using h

/-- Logarithms of products split under mixed nonvanishing and positivity evidence. -/
example (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b := by
  cas

end CAS.Examples.DomainConventions
