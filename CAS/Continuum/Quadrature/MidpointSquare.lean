/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounding a squared function from its midpoint value

A small value at the midpoint does not by itself control an integral. A derivative
bound fills the gap: it controls how far the function can move between the sample
and each point of the panel. Integrating that distance squared exactly gives
`(b - a)³ / 12` (`integral_sq_sub_midpoint`) instead of the largest distance times the panel
width. `integral_sq_le_of_midpoint_deviation` is the resulting bound on `∫ f ^ 2`.

The approximation theorem also allows the derivative bound to belong to a nearby
function. Its uniform error is counted at both the sample and the integration point.
No derivative at a panel endpoint is needed.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

private theorem add_sq_le_weighted (u v : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (u + v) ^ 2 ≤ (1 + θ) * u ^ 2 + (1 + 1 / θ) * v ^ 2 := by
  have key : (1 + θ) * u ^ 2 + (1 + 1 / θ) * v ^ 2 - (u + v) ^ 2 = (θ * u - v) ^ 2 / θ := by
    field_simp
    ring
  rw [← sub_nonneg, key]
  positivity

/-- A derivative bound for an approximation controls variation of the original
function about the panel midpoint, with the approximation error counted twice. -/
theorem abs_sub_midpoint_le_of_approximation
    {f g : ℝ → ℝ} {a b M δ : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ioo a b, |deriv f x| ≤ M)
    (herror : ∀ x ∈ Ioo a b, |g x - f x| ≤ δ)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    |g x - g ((a + b) / 2)| ≤ M * |x - (a + b) / 2| + 2 * δ := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hvariation := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le
    hf (by simpa only [Real.norm_eq_abs] using hderiv) hm hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hvariation
  linarith [abs_sub_le (g x) (f x) (g ((a + b) / 2)),
    abs_sub_le (f x) (f ((a + b) / 2)) (g ((a + b) / 2)), herror x hx, herror _ hm,
    abs_sub_comm (f ((a + b) / 2)) (g ((a + b) / 2))]

/-- The exact second moment of a panel about its midpoint. -/
theorem integral_sq_sub_midpoint (a b : ℝ) :
    (∫ x in a..b, (x - (a + b) / 2) ^ 2) = (b - a) ^ 3 / 12 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2),
    integral_pow]
  norm_num
  ring

/-- Integrate a quadratic bound centered at the midpoint. The inequality is needed
only in the open panel, so knot values do not affect the conclusion. -/
theorem integral_sq_le_of_midpoint_bound
    {g : ℝ → ℝ} {a b A B C : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable (fun x ↦ g x ^ 2) volume a b)
    (hbound : ∀ x ∈ Ioo a b,
      g x ^ 2 ≤ A * g ((a + b) / 2) ^ 2 + B * (x - (a + b) / 2) ^ 2 + C) :
    (∫ x in a..b, g x ^ 2) ≤
      A * (b - a) * g ((a + b) / 2) ^ 2 + B * (b - a) ^ 3 / 12 + C * (b - a) := by
  have hquad : Continuous (fun x : ℝ ↦ B * (x - (a + b) / 2) ^ 2) := by fun_prop
  have hmajorant : IntervalIntegrable
      (fun x ↦ A * g ((a + b) / 2) ^ 2 + B * (x - (a + b) / 2) ^ 2 + C) volume a b :=
    ((continuous_const.add hquad).add continuous_const).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hab hg hmajorant hbound
  rw [intervalIntegral.integral_add
      (f := fun x ↦ A * g ((a + b) / 2) ^ 2 + B * (x - (a + b) / 2) ^ 2)
      (g := fun _ ↦ C)
      ((continuous_const.add hquad).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_add
      (f := fun _ ↦ A * g ((a + b) / 2) ^ 2)
      (g := fun x ↦ B * (x - (a + b) / 2) ^ 2)
      (continuous_const.intervalIntegrable _ _)
      (hquad.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul B (fun x ↦ (x - (a + b) / 2) ^ 2),
    integral_sq_sub_midpoint,
    intervalIntegral.integral_const, intervalIntegral.integral_const] at hle
  simpa only [smul_eq_mul] using hle.trans_eq (by ring)

/-- A midpoint sample, a linear variation bound, and an additive error give an
upper bound on the squared integral. The positive parameters `α` and `β` choose
the two Young inequalities, allowing the sample and variation budgets to be balanced. -/
theorem integral_sq_le_of_midpoint_deviation
    {g : ℝ → ℝ} {a b M ε α β : ℝ} (hab : a ≤ b)
    (hα : 0 < α) (hβ : 0 < β)
    (hg : IntervalIntegrable (fun x ↦ g x ^ 2) volume a b)
    (hvariation : ∀ x ∈ Ioo a b,
      |g x - g ((a + b) / 2)| ≤ M * |x - (a + b) / 2| + ε) :
    (∫ x in a..b, g x ^ 2) ≤
      (1 + α) * (b - a) * g ((a + b) / 2) ^ 2 +
        (1 + 1 / α) * (1 + β) * M ^ 2 * (b - a) ^ 3 / 12 +
        (1 + 1 / α) * (1 + 1 / β) * ε ^ 2 * (b - a) := by
  apply integral_sq_le_of_midpoint_bound hab hg
  intro x hx
  have hfirst := add_sq_le_weighted (g ((a + b) / 2)) (g x - g ((a + b) / 2)) hα
  have hdiff : (g x - g ((a + b) / 2)) ^ 2 ≤ (M * |x - (a + b) / 2| + ε) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hvariation x hx) 2
  have hweighted := mul_le_mul_of_nonneg_left
    (hdiff.trans (add_sq_le_weighted (M * |x - (a + b) / 2|) ε hβ))
    (by positivity : (0 : ℝ) ≤ 1 + 1 / α)
  rw [mul_pow, sq_abs] at hweighted
  nlinarith only [hfirst, hweighted]

end CAS.Continuum
