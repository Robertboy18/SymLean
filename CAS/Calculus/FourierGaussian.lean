/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Fourier transform of a real Gaussian

In Mathlib's convention `𝓕 f ξ = ∫ x, e ^ (-2 π i x ξ) f x`
(`Real.fourier_real_eq_integral_exp_smul`; Mathematica's `FourierParameters -> {0, -2 Pi}`),
for `α > 0` and real `β`, `γ`, `c`,

`𝓕 (c e ^ (-α x ^ 2 + β x + γ)) ξ = c (π / α) ^ (1 / 2) e ^ ((β - 2 π i ξ) ^ 2 / (4 α) + γ)`
`  = c √(π / α) e ^ ((β ^ 2 - 4 π ^ 2 ξ ^ 2) / (4 α) + γ) e ^ (-i π β ξ / α)`.

## Main results

* `fourier_gaussian_real`: the transform with a complex square root and exponent.
* `fourier_gaussian_real'`: the same value with real factors and a phase `e ^ (-i π β ξ / α)`.

## Implementation notes

The analysis is Mathlib's. After `Real.fourier_real_eq_integral_exp_smul` the integrand is
`c e ^ (-α x ^ 2 + (β - 2 π i ξ) x + γ)`, and `integral_cexp_quadratic`
(`∫ e ^ (b x ^ 2 + c x + d) = (π / -b) ^ (1 / 2) e ^ (d - c ^ 2 / (4 b))` for `re b < 0`)
evaluates it, the computation behind Mathlib's `fourier_gaussian_pi'`. We prove the real form
from `integral_cexp_quadratic` directly, since `fourier_gaussian_pi'` is stated for the exponent
`-π b x ^ 2 + 2 π c x`, while `#cas [fourierTransform x ξ]` (`CAS.Command.FourierTransform`) reads
`c e ^ (-α x ^ 2 + β x + γ)` with rational parameters and prints real factors.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>. The declarations
  `Real.fourier_real_eq_integral_exp_smul` and `integral_cexp_quadratic`.
-/

public section

namespace CAS.Calculus.FourierGaussian

open Complex MeasureTheory
open scoped FourierTransform

/-- The Fourier transform of `c e ^ (-α x ^ 2 + β x + γ)` (`α > 0`) in Mathlib's convention
`𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x`: `c (π / α) ^ (1 / 2) e ^ ((β - 2 π i ξ) ^ 2 / (4 α) + γ)`. -/
theorem fourier_gaussian_real {α : ℝ} (hα : 0 < α) (β γ c ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ ((c * Real.exp (-α * x ^ 2 + β * x + γ) : ℝ) : ℂ)) ξ =
      c * ((Real.pi : ℂ) / α) ^ (1 / 2 : ℂ) *
        cexp ((β - 2 * Real.pi * ξ * I) ^ 2 / (4 * α) + γ) := by
  have hb : (-(α : ℂ)).re < 0 := by simp [hα]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h (x : ℝ) : cexp (↑(-2 * Real.pi * x * ξ) * I) •
      ((c * Real.exp (-α * x ^ 2 + β * x + γ) : ℝ) : ℂ) =
      c * cexp (-(α : ℂ) * x ^ 2 + (β - 2 * Real.pi * ξ * I) * x + γ) := by
    rw [smul_eq_mul, ofReal_mul c, ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h, integral_const_mul, integral_cexp_quadratic hb, neg_neg]
  have e : ∀ z : ℂ, (γ : ℂ) - z / (4 * -(α : ℂ)) = z / (4 * α) + γ := fun z ↦ by
    rw [mul_neg, div_neg, sub_neg_eq_add, add_comm]
  simp only [e]
  ring

/-- `fourier_gaussian_real` with real factors:
`𝓕 (c e ^ (-α x ^ 2 + β x + γ)) ξ = c √(π / α) e ^ ((β ^ 2 - 4 π ^ 2 ξ ^ 2) / (4 α) + γ)
e ^ (-i π β ξ / α)`. -/
theorem fourier_gaussian_real' {α : ℝ} (hα : 0 < α) (β γ c ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ ((c * Real.exp (-α * x ^ 2 + β * x + γ) : ℝ) : ℂ)) ξ =
      ((c * Real.sqrt (Real.pi / α) *
        Real.exp ((β ^ 2 - 4 * Real.pi ^ 2 * ξ ^ 2) / (4 * α) + γ) : ℝ) : ℂ) *
        cexp (-(Real.pi * β * ξ / α : ℝ) * I) := by
  rw [fourier_gaussian_real hα]
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  have hs : ((Real.pi : ℂ) / α) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / α) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (div_nonneg Real.pi_pos.le hα.le), ofReal_div]
    norm_num
  have e : cexp ((β - 2 * Real.pi * ξ * I) ^ 2 / (4 * α) + γ) =
      cexp (((β ^ 2 - 4 * Real.pi ^ 2 * ξ ^ 2) / (4 * α) + γ : ℝ)) *
        cexp (-(Real.pi * β * ξ / α : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hs, e, ofReal_mul, ofReal_mul, ofReal_exp]
  ring

end CAS.Calculus.FourierGaussian
