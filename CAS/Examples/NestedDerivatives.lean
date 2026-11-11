/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ExactTactic

/-!
# Nested derivatives and calculus atoms in exact `cas` proofs

`cas` proves nested derivatives of `sinh` and `cosh`, and the derivative of `tanh`, which
are reflected through their exponential identities: `deriv (deriv sinh) = sinh`, a third
derivative, and the `HasDerivAt`, `HasDerivWithinAt` and `DifferentiableAt` shapes of an inner
derivative. The checked inner derivative is transported back to the ordinary function
before it is rewritten. When the inner function is not valid everywhere, the transport holds on
a neighbourhood of the point, so a nested logarithm or absolute value needs only `x ≠ 0`. Bare
`cas` closes the residual of a separated harmonic mode.

The final examples rearrange integral and derivative values algebraically,
without calculating them or importing the integration frontend.
-/

@[expose] public section

namespace CAS.Examples.NestedDerivatives

/-- Nested `deriv` equalities use the checked exponential representation of `sinh`. -/
theorem deriv_deriv_sinh (x : ℝ) :
    deriv (deriv Real.sinh) x = Real.sinh x := by
  cas

/-- Frozen parameters and an applied inner derivative use the same transport. -/
theorem deriv_deriv_cosh_affine (a b x : ℝ) :
    deriv (fun t ↦ deriv (fun s ↦ Real.cosh (a * s + b)) t) x =
      a ^ 2 * Real.cosh (a * x + b) := by
  cas

/-- Repeated transport composes when more than one inner derivative is eliminated. -/
theorem deriv_deriv_deriv_sinh (x : ℝ) :
    deriv (deriv (deriv Real.sinh)) x = Real.cosh x := by
  cas

/-- A `HasDerivAt` goal retains the derivative certificate after inner differentiation. -/
theorem hasDerivAt_deriv_sinh (x : ℝ) :
    HasDerivAt (deriv Real.sinh) (Real.sinh x) x := by
  cas

/-- The exponential quotient rule for `tanh` normalizes to the reciprocal square of `cosh`. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  cas

/-- The nested derivative certificate restricts to any set, including at boundary points. -/
theorem hasDerivWithinAt_deriv_cosh (s : Set ℝ) (x : ℝ) :
    HasDerivWithinAt (deriv Real.cosh) (Real.cosh x) s x := by
  cas

/-- Differentiability of a nested derivative needs no stated derivative value. -/
theorem differentiableAt_deriv_cosh (x : ℝ) :
    DifferentiableAt ℝ (deriv Real.cosh) x := by
  cas

/-- A separated harmonic mode exercises the derivative rewriting route of bare `cas`. -/
theorem harmonic_mode (k t x : ℝ) :
    deriv (deriv (fun s ↦ Real.sinh (k * s) * Real.sin (k * x))) t +
      deriv (deriv (fun y ↦ Real.sinh (k * t) * Real.sin (k * y))) x = 0 := by
  cas

/-- A nested logarithm needs its argument nonzero only at the point: the inner derivative is
transported on a neighbourhood of `x`. -/
theorem deriv_deriv_log_two_mul (x : ℝ) (hx : x ≠ 0) :
    deriv (deriv (fun t : ℝ ↦ Real.log (2 * t))) x = -(x ^ 2)⁻¹ := by
  cas using hx

/-- The second derivative of `|t|` vanishes at every point other than `0`. -/
theorem deriv_deriv_abs (x : ℝ) (hx : x ≠ 0) : deriv (deriv (fun t : ℝ ↦ |t|)) x = 0 := by
  cas using hx

section IntegralAlgebra

open scoped Interval
open MeasureTheory

/-- Integral values commute in a general normed space and with an arbitrary measure. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (c : E) (μ : Measure ℝ) :
    (∫ x in a..b, f x ∂μ) + c = c + ∫ x in a..b, f x ∂μ := by
  cas

/-- Regrouping summands containing a derivative does not require differentiating the function. -/
example (f : ℝ → ℝ) (a b c : ℝ) :
    (deriv f a + b) + c = deriv f a + (b + c) := by
  cas

end IntegralAlgebra

end CAS.Examples.NestedDerivatives
