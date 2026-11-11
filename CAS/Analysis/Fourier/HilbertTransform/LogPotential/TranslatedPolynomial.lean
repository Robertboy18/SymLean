/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Fourier.HilbertTransform.LogPotential.Polynomial
public import CAS.Analysis.SpecialFunctions.Log.Bounds

/-!
# Finite translated polynomial logarithm integrals

The integral of `(y - x)^n log (x - y)` over a finite panel `[a, b]` is a difference of
values of the log-monomial primitive at `b - x` and `a - x` (`integral_shifted_pow_mul_log`).
Expanding a polynomial in powers of `y - x` gives the exact panel integral `polynomialLogPanel`
(`polynomialLogPanel_eq_sum_of_eval`). A uniform bound `B` on the polynomial also transfers the
L¹ modulus of the logarithm to its weighted panel integral: `abs_polynomialLogPanel_sub_le`
bounds the change of `polynomialLogPanel p a b x` in `x` by `B` times
`∫ y in a..b, |log (x - y) - log (m - y)|`, which `integral_abs_log_sub_le` bounds in turn.
-/

@[expose] public section

open MeasureTheory Set
open scoped Polynomial

namespace CAS.Analysis

/-- Each translated monomial-log integrand is absolutely integrable on any finite panel. -/
theorem intervalIntegrable_shifted_pow_mul_log (n : ℕ) (a b x : ℝ) :
    IntervalIntegrable (fun y ↦ (y - x) ^ n * Real.log (x - y)) volume a b := by
  have h := (intervalIntegrable_pow_mul_log n (a - x) (b - x)).comp_sub_right x
  simp only [sub_add_cancel] at h
  simpa only [← neg_sub x, Real.log_neg_eq_log] using h

/-- Exact integration of a monomial centered at the logarithmic singularity. -/
theorem integral_shifted_pow_mul_log (n : ℕ) (a b x : ℝ) :
    (∫ y in a..b, (y - x) ^ n * Real.log (x - y)) =
      logMonomialPrimitive n (b - x) - logMonomialPrimitive n (a - x) := by
  simp_rw [← Real.log_neg_eq_log (x - _), neg_sub]
  rw [intervalIntegral.integral_comp_sub_right
    (f := fun t ↦ t ^ n * Real.log t), integral_pow_mul_log]

/-- A finite translated coefficient representation determines the exact log panel. -/
theorem polynomialLogPanel_eq_sum_of_eval {n : ℕ} (p : ℝ[X]) (c : Fin n → ℝ)
    (a b x : ℝ) (hc : ∀ y, p.eval y = ∑ i : Fin n, c i * (y - x) ^ i.val) :
    polynomialLogPanel p a b x =
      ∑ i : Fin n, c i *
        (logMonomialPrimitive i.val (b - x) - logMonomialPrimitive i.val (a - x)) := by
  rw [← integral_polynomial_mul_log_sub]
  simp_rw [hc, Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, integral_shifted_pow_mul_log]
  · intro i _
    exact (intervalIntegrable_shifted_pow_mul_log i.val a b x).const_mul (c i)

/-- A bounded polynomial weight multiplies the L¹ translation error of the kernel. -/
theorem abs_polynomialLogPanel_sub_le (p : ℝ[X]) {a b x m B : ℝ}
    (hab : a ≤ b) (hp : ∀ y ∈ Icc a b, |p.eval y| ≤ B) :
    |polynomialLogPanel p a b x - polynomialLogPanel p a b m| ≤
      B * ∫ y in a..b, |Real.log (x - y) - Real.log (m - y)| := by
  have hlog (z : ℝ) :
      IntervalIntegrable (fun y ↦ p.eval y * Real.log (z - y)) volume a b := by
    have h := intervalIntegrable_polynomial_mul_log p a b z
    simpa only [← neg_sub z, Real.log_neg_eq_log] using h
  rw [← integral_polynomial_mul_log_sub, ← integral_polynomial_mul_log_sub,
    ← intervalIntegral.integral_sub (hlog x) (hlog m)]
  simp_rw [← mul_sub]
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (show ∀ᵐ y ∂volume, y ∈ Ioc a b →
        ‖p.eval y * (Real.log (x - y) - Real.log (m - y))‖ ≤
          B * |Real.log (x - y) - Real.log (m - y)| from
      Filter.Eventually.of_forall fun y hy ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_right (hp y ⟨hy.1.le, hy.2⟩) (abs_nonneg _))
    ((intervalIntegrable_abs_log_sub a b x m).const_mul B)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using h

end CAS.Analysis
