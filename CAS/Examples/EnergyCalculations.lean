/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.IntegrationTactic

/-!
# Elementary calculations from evolution estimates

These examples calculate terms from energy and continuation estimates: Young's
inequality for absorbing a mixed term, a product of square roots, derivatives
with a constant divisor and with an opaque derivative coefficient, and a slot
reference profile.
The time integrals include arbitrary natural powers and the integrable singularity
`t ^ (-3/4)` at zero.
-/

@[expose] public noncomputable section

namespace CAS.Examples.EnergyCalculations

/-- The quadratic Young bound used to absorb a mixed energy term. -/
theorem quadratic_young (x y ν : ℝ) (hν : 0 < ν) :
    2 * x * y ≤ ν * x ^ 2 + ν⁻¹ * y ^ 2 := by
  cas

/-- A product of square roots requires a sign condition. -/
example (x y : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
  cas

/-- Constant scalar division is differentiable also at a zero divisor. -/
theorem derivative_constant_divisor (ell x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.exp (t / ell)) (Real.exp (x / ell) / ell) x := by
  cas

/-- Fixed derivative values stay opaque alongside an actual nested derivative. -/
theorem derivative_mixed_coefficient (u : ℝ → ℝ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ deriv u x * deriv (fun s : ℝ ↦ s ^ 2) t)
      (2 * deriv u x) y := by
  cas

/-- Interval membership supplies its two inequalities to arithmetic. -/
theorem interval_lower_bound (L x : ℝ) (hx : x ∈ Set.Ioo 0 L) :
    -L < x := by
  cas

/-- The slot magnitude `u / 2 + u v / ℓ`. -/
def slotMagnitude (u ell v : ℝ) : ℝ := u / 2 + u * v / ell

/-- The reference profile `c √(1 + s²)`, where `s` is the slot magnitude. -/
def referenceProfile (c u ell v : ℝ) : ℝ :=
  c * Real.sqrt (1 + slotMagnitude u ell v ^ 2)

/-- The reference profile has the expected logarithmic derivative, including `ell = 0`. -/
theorem derivative_referenceProfile (c u ell v : ℝ) :
    HasDerivAt (referenceProfile c u ell)
      (slotMagnitude u ell v * (u / ell) / (1 + slotMagnitude u ell v ^ 2) *
        referenceProfile c u ell v) v := by
  cas

/-- The symbolic natural-power formula retains an arbitrary exponent. -/
example (n : ℕ) (a b : ℝ) :
    (∫ t : ℝ in a..b, t ^ n) = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  cas

/-- The endpoint singularity in the whole-space Gaussian estimate is integrable. -/
theorem singular_power_integral (ε K : ℝ) :
    (∫ t : ℝ in 0..ε, (3 / 4 : ℝ) * t ^ (-(3 : ℝ) / 4) * K) =
      3 * ε ^ (1 / 4 : ℝ) * K := by
  cas

end CAS.Examples.EnergyCalculations
