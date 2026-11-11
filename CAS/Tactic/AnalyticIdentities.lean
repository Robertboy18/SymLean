/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Analytic identities used by the tactics

The first lemmas restate `Real.sin_sq_add_cos_sq` in the shapes
left behind when the quotient rule is applied to `sin / cos`, so that the derivative
frontends (`CAS/Tactic/DerivativeBridge.lean`) can recognise `1 / cos t ^ 2` after lowering
`tan`.

The others are the rewrites of the elementary-rewrites stage of bare `cas`
(`CAS.Tactic.ElementaryRewrites`), each stated with the hypothesis it needs: a multiple
angle `k * a` peeled to `(k - 1) * a + a` once `k = (k - 1) + 1` is checked, and
`exp (k * log u) = u ^ k` for a natural `k` under `0 < u` (or `|u| ^ k` under `u ≠ 0`) and for a
real `k` under `0 < u`.
-/

@[expose] public section

namespace CAS.Tactic.AnalyticIdentities

/-- The quotient-rule residue of `tan` in product form collapses to `(cos t)⁻¹ ^ 2 * a`. -/
theorem tangent_derivative_mul_normalize (t a : ℝ) :
    Real.cos t ^ 2 * (Real.cos t)⁻¹ ^ 2 * a +
        (Real.cos t)⁻¹ ^ 2 * Real.sin t ^ 2 * a =
      (Real.cos t)⁻¹ ^ 2 * a := by
  linear_combination (Real.cos t)⁻¹ ^ 2 * a * Real.sin_sq_add_cos_sq t

/-- The quotient-rule residue of `tan` in division form collapses to `a / cos t ^ 2`. -/
theorem tangent_derivative_div_normalize (t a : ℝ) :
    (Real.cos t * a * Real.cos t + Real.sin t * Real.sin t * a) /
        Real.cos t ^ 2 =
      a / Real.cos t ^ 2 :=
  congrArg (· / Real.cos t ^ 2) (by linear_combination a * Real.sin_sq_add_cos_sq t)

/-- A scalar splits along `sin² + cos² = 1`, the shape met when matching a tangent
derivative against a stated coefficient. -/
theorem tangent_scaled_sum_normalize (t a : ℝ) :
    a = Real.cos t ^ 2 * a + Real.sin t ^ 2 * a := by
  linear_combination -a * Real.sin_sq_add_cos_sq t

/-- The sine of a multiple angle from the previous multiple. -/
theorem sin_mul_of_eq_add_one {k m : ℝ} (h : k = m + 1) (a : ℝ) :
    Real.sin (k * a) = Real.sin (m * a) * Real.cos a + Real.cos (m * a) * Real.sin a := by
  rw [h, add_mul, one_mul, Real.sin_add]

/-- The cosine of a multiple angle from the previous multiple. -/
theorem cos_mul_of_eq_add_one {k m : ℝ} (h : k = m + 1) (a : ℝ) :
    Real.cos (k * a) = Real.cos (m * a) * Real.cos a - Real.sin (m * a) * Real.sin a := by
  rw [h, add_mul, one_mul, Real.cos_add]

/-- `exp (k * log u) = u ^ k` for a natural `k` and `0 < u`. -/
theorem exp_mul_log_of_pos {k : ℝ} {n : ℕ} (hk : k = n) {u : ℝ} (hu : 0 < u) :
    Real.exp (k * Real.log u) = u ^ n := by
  rw [hk, Real.exp_nat_mul, Real.exp_log hu]

/-- `exp (log u * k) = u ^ k` for a natural `k` and `0 < u`. -/
theorem exp_log_mul_of_pos {k : ℝ} {n : ℕ} (hk : k = n) {u : ℝ} (hu : 0 < u) :
    Real.exp (Real.log u * k) = u ^ n := by
  rw [mul_comm, exp_mul_log_of_pos hk hu]

/-- `exp (k * log u) = |u| ^ k` for a natural `k` and `u ≠ 0`. -/
theorem exp_mul_log_of_ne_zero {k : ℝ} {n : ℕ} (hk : k = n) {u : ℝ} (hu : u ≠ 0) :
    Real.exp (k * Real.log u) = |u| ^ n := by
  rw [hk, Real.exp_nat_mul, Real.exp_log_eq_abs hu]

/-- `exp (log u * k) = |u| ^ k` for a natural `k` and `u ≠ 0`. -/
theorem exp_log_mul_of_ne_zero {k : ℝ} {n : ℕ} (hk : k = n) {u : ℝ} (hu : u ≠ 0) :
    Real.exp (Real.log u * k) = |u| ^ n := by
  rw [mul_comm, exp_mul_log_of_ne_zero hk hu]

/-- `exp (k * log u) = u ^ k` as a real power for `0 < u`. -/
theorem exp_mul_log_eq_rpow (k : ℝ) {u : ℝ} (hu : 0 < u) :
    Real.exp (k * Real.log u) = u ^ k := by
  rw [Real.rpow_def_of_pos hu, mul_comm]

end CAS.Tactic.AnalyticIdentities
