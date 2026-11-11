/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Integral

/-!
# A mean-value principle for integrated remainder formulas

Suppose `r x = d y * φ x` on `[a, b]`, where the point `y = y x` may depend on `x`, with `d`
continuous, `φ ≥ 0` and `∫ φ > 0`. Then `∫ r = d ξ * ∫ φ` for a single `ξ ∈ [a, b]`. The
minimum and maximum of `d` bound the ratio `∫ r / ∫ φ`, and the intermediate value theorem
supplies `ξ` (`integral_eq_value_mul_of_pointwise_image`). The pointwise choice `x ↦ y x`
need not be measurable. `Remainder` uses this to pass from the pointwise Hermite remainder to
the integrated Gaussian remainder.

## References

* Josef Stoer and Roland Bulirsch, *Introduction to Numerical Analysis*, 3rd ed., Texts in Applied
  Mathematics 12, Springer, New York, 2002, <https://doi.org/10.1007/978-0-387-21738-3>. §3.6, where
  the mean value theorem for integrals turns the pointwise Hermite remainder into the Gaussian one.
-/

@[expose] public section

namespace CAS.Continuum

open Set MeasureTheory

/-- If at each `x ∈ [a, b]` there is `y ∈ [a, b]` with `r x = d y * φ x`, then
`∫ r = d ξ * ∫ φ` for a single `ξ ∈ [a, b]`. Requires `d` continuous on `[a, b]`, `φ ≥ 0`
there and `∫ φ > 0`. The extrema of `d` bound `∫ r / ∫ φ`, and the intermediate value theorem
picks `ξ`. -/
theorem integral_eq_value_mul_of_pointwise_image {a b : ℝ} (hab : a < b)
    {r φ d : ℝ → ℝ}
    (hr : IntervalIntegrable r volume a b)
    (hφ : IntervalIntegrable φ volume a b)
    (hd : ContinuousOn d (Icc a b))
    (hφnonneg : ∀ x ∈ Icc a b, 0 ≤ φ x)
    (hφpos : 0 < ∫ x in a..b, φ x)
    (himage : ∀ x ∈ Icc a b, ∃ y ∈ Icc a b, r x = d y * φ x) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, r x) = d ξ * ∫ x in a..b, φ x := by
  obtain ⟨l, hl, hlmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hd
  obtain ⟨u, hu, humax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hd
  have hlo : d l * (∫ x in a..b, φ x) ≤ ∫ x in a..b, r x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab.le (hφ.const_mul _) hr fun x hx ↦ ?_
    obtain ⟨y, hy, heq⟩ := himage x hx
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hlmin hy) (hφnonneg x hx)
  have hhi : (∫ x in a..b, r x) ≤ d u * ∫ x in a..b, φ x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab.le hr (hφ.const_mul _) fun x hx ↦ ?_
    obtain ⟨y, hy, heq⟩ := himage x hx
    rw [heq]
    exact mul_le_mul_of_nonneg_right (humax hy) (hφnonneg x hx)
  obtain ⟨ξ, hξ, heq⟩ := isPreconnected_Icc.intermediate_value hl hu hd
    ⟨(le_div_iff₀ hφpos).mpr hlo, (div_le_iff₀ hφpos).mpr hhi⟩
  exact ⟨ξ, hξ, by rw [heq, div_mul_cancel₀ _ (ne_of_gt hφpos)]⟩

end CAS.Continuum
