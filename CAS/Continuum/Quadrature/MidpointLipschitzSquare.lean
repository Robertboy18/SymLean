/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.MidpointSquare

/-!
# A squared midpoint bound retaining the mixed term

When the midpoint value and its local variation are both small, integrating
their product directly is sharper than separating them with Young's inequality.
The first absolute moment of a panel about its midpoint is `(b - a)² / 4`
(`integral_abs_sub_midpoint`), and its second moment is `(b - a)³ / 12`
(`integral_sq_sub_midpoint`). These two moments give the bound
`integral_sq_le_of_midpoint_abs_bound`, which can be summed with a different slope estimate
on each panel.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- The exact first absolute moment about the midpoint of an ordered interval. -/
theorem integral_abs_sub_midpoint {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, |x - (a + b) / 2|) = (b - a) ^ 2 / 4 := by
  set m := (a + b) / 2 with hm
  have ham : a ≤ m := by linarith
  have hmb : m ≤ b := by linarith
  have hi (c d : ℝ) : IntervalIntegrable (fun x : ℝ ↦ |x - m|) volume c d :=
    (continuous_id.sub continuous_const).abs.intervalIntegrable _ _
  have hl : (∫ x in a..m, |x - m|) = ∫ x in a..m, m - x :=
    intervalIntegral.integral_congr_uIoo fun x hx ↦ by
      rw [uIoo_of_le ham] at hx
      exact (abs_sub_comm x m).trans (abs_of_pos (sub_pos.mpr hx.2))
  have hr : (∫ x in m..b, |x - m|) = ∫ x in m..b, x - m :=
    intervalIntegral.integral_congr_uIoo fun x hx ↦ by
      rw [uIoo_of_le hmb] at hx
      exact abs_of_pos (sub_pos.mpr hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a m) (hi m b), hl, hr,
    intervalIntegral.integral_comp_sub_left (fun x ↦ x),
    intervalIntegral.integral_comp_sub_right (fun x ↦ x), integral_id, integral_id, hm]
  ring

/-- Integrate the square of a midpoint-centered linear majorant exactly. -/
theorem integral_sq_le_of_midpoint_abs_bound
    {g : ℝ → ℝ} {a b A M : ℝ} (hab : a ≤ b)
    (hbound : ∀ x ∈ Ioo a b, |g x| ≤ A + M * |x - (a + b) / 2|) :
    (∫ x in a..b, g x ^ 2) ≤
      (b - a) * A ^ 2 + A * M * (b - a) ^ 2 / 2 + M ^ 2 * (b - a) ^ 3 / 12 := by
  by_cases hg : IntervalIntegrable (fun x ↦ g x ^ 2) volume a b
  swap
  · rw [intervalIntegral.integral_undef hg]
    have hL : 0 ≤ b - a := sub_nonneg.mpr hab
    nlinarith [mul_nonneg hL (sq_nonneg (A + M * (b - a) / 4)),
      mul_nonneg hL (sq_nonneg (M * (b - a)))]
  let m := (a + b) / 2
  have hlin : Continuous (fun x : ℝ ↦ 2 * A * M * |x - m|) := by fun_prop
  have hquad : Continuous (fun x : ℝ ↦ M ^ 2 * (x - m) ^ 2) := by fun_prop
  have hmajorant : IntervalIntegrable
      (fun x : ℝ ↦ A ^ 2 + 2 * A * M * |x - m| + M ^ 2 * (x - m) ^ 2) volume a b :=
    ((continuous_const.add hlin).add hquad).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hab hg hmajorant
    (fun x hx ↦ by
      have h := pow_le_pow_left₀ (abs_nonneg (g x)) (hbound x hx) 2
      rw [sq_abs] at h
      nlinarith only [h, sq_abs (x - m)])
  rw [intervalIntegral.integral_add
      (f := fun x : ℝ ↦ A ^ 2 + 2 * A * M * |x - m|)
      (g := fun x : ℝ ↦ M ^ 2 * (x - m) ^ 2)
      ((continuous_const.add hlin).intervalIntegrable _ _) (hquad.intervalIntegrable _ _),
    intervalIntegral.integral_add
      (f := fun _ : ℝ ↦ A ^ 2) (g := fun x : ℝ ↦ 2 * A * M * |x - m|)
      (continuous_const.intervalIntegrable _ _)
      (hlin.intervalIntegrable _ _),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_abs_sub_midpoint hab, integral_sq_sub_midpoint] at hle
  simpa only [smul_eq_mul] using hle.trans_eq (by ring)

end CAS.Continuum
