/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.PanelRule
public import CAS.Continuum.Quadrature.PeanoKernel
public import CAS.Continuum.Quadrature.Trapezoidal

/-!
# The trapezoidal and midpoint rules as second-order panel rules

The trapezoidal rule `(b-a) (f a + f b) / 2` and the midpoint rule `(b-a) f((a+b)/2)` are the
two classical rules exact on linear polynomials.  Their Peano kernels have one sign on each
panel, which gives the sharp one-panel estimates

`‖∫ₐᵇ f - T(f)‖ ≤ M (b-a)³ / 12`,   `‖∫ₐᵇ f - M(f)‖ ≤ M (b-a)³ / 24`

for `‖f''‖ ≤ M` on `[a,b]`.  Both rules are therefore instances of `PanelRule 2`, and their
composite, planned and adaptive versions come from that structure.

## Main definitions

* `trapezoidRule`, `midpointRule`: the normalized rules on `[0,1]`.
* `trapezoidRule.secondOrder`, `midpointRule.secondOrder`: the `PanelRule 2` instances with
  denominators `12` and `24`.

## Main results

* `norm_integral_sub_trapezoidRule_valueOn_le`, `norm_integral_sub_midpointRule_valueOn_le`:
  the sharp one-panel estimates.
* `integral_le_midpoint_of_second_deriv_bound`: an upper bound stated using ordinary
  second derivatives on a closed panel.

## Implementation notes

We write both kernels down. The trapezoid kernel `(x-a)(x-b)/2` is a polynomial on all of `ℝ`,
so one application of `integral_mul_iteratedDerivWithin_two` gives the error identity; the kernel
is nonpositive on `[a,b]` with mass `-(b-a)³/12`. The midpoint kernel is `(x-a)²/2` on the left
half and `(x-b)²/2` on the right, nonnegative with mass `(b-a)³/48` on each half, so we apply
the identity on each half and add. The trapezoid kernel is the one Peano writes on p. 562 of his
note, and the constants `12` and `24` are classical; the Lean proofs are ours.

## References

* Giuseppe Peano, "Resto nelle formule di quadratura, espresso con un integrale definito",
  *Atti della Reale Accademia dei Lincei, Rendiconti, Classe di scienze fisiche, matematiche e
  naturali*, series 5, 22, first semester (1913), pp. 562-569,
  <https://archive.org/details/rendiconti-lincei_1913-05-04_22_part-1/page/n33/mode/1up>.
  The trapezoidal remainder `-½ ∫ₐᵇ (x-a)(b-x) f''(x) dx` on p. 562.
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equation (3.5.1) for the trapezoidal rule and its error term
  `-(b-a)³f''(ξ)/12`.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- The trapezoidal rule on `[0,1]`: weights `1/2` at both endpoints. -/
noncomputable def trapezoidRule : QuadratureRule where
  terms := [((1 : ℝ) / 2, 0), ((1 : ℝ) / 2, 1)]
  nodes_mem_unit := by
    intro term hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with hterm | hterm <;> subst term <;> norm_num

/-- The midpoint rule on `[0,1]`: weight `1` at `1/2`. -/
noncomputable def midpointRule : QuadratureRule where
  terms := [((1 : ℝ), 1 / 2)]
  nodes_mem_unit := by
    intro term hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    subst term
    norm_num

/-- The transported trapezoid value on `[a,b]` is `(b-a) (f a + f b) / 2`. -/
theorem trapezoidRule_valueOn_eq_formula (f : ℝ → ℝ) (a b : ℝ) :
    trapezoidRule.valueOn f a b = (b - a) * (f a + f b) / 2 := by
  norm_num [QuadratureRule.valueOn, QuadratureRule.termsOn, trapezoidRule, weightedSum]
  ring

/-- The transported midpoint value on `[a,b]` is `(b-a) f((a+b)/2)`. -/
theorem midpointRule_valueOn_eq_formula (f : ℝ → ℝ) (a b : ℝ) :
    midpointRule.valueOn f a b = (b - a) * f ((a + b) / 2) := by
  norm_num [QuadratureRule.valueOn, QuadratureRule.termsOn, midpointRule, weightedSum]
  rw [show a + 1 / 2 * (b - a) = (a + b) / 2 by ring]
  exact Or.inl rfl

namespace trapezoidRule

/-- The trapezoid rule has the exact normalized moments of degrees zero and one. -/
theorem exactUpTo_one : trapezoidRule.ExactUpTo 1 := by
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.ExactUpTo, QuadratureRule.moment,
      QuadratureRule.normalizedValue, trapezoidRule, weightedSum]

end trapezoidRule

namespace midpointRule

/-- The midpoint rule has the exact normalized moments of degrees zero and one. -/
theorem exactUpTo_one : midpointRule.ExactUpTo 1 := by
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.ExactUpTo, QuadratureRule.moment,
      QuadratureRule.normalizedValue, midpointRule, weightedSum]

end midpointRule

/-! ### The trapezoid kernel -/

private noncomputable def trapezoidKernel (a b x : ℝ) : ℝ :=
  (x - a) * (x - b) / 2

private noncomputable def trapezoidKernelOne (a b x : ℝ) : ℝ :=
  x - (a + b) / 2

private noncomputable def trapezoidKernelPrimitive (a b x : ℝ) : ℝ :=
  (x - a) ^ 3 / 6 - (b - a) * (x - a) ^ 2 / 4

private theorem trapezoidKernel_hasDerivAt (a b x : ℝ) :
    HasDerivAt (trapezoidKernel a b) (trapezoidKernelOne a b x) x := by
  unfold trapezoidKernel trapezoidKernelOne
  convert (((hasDerivAt_id' x).sub_const a).mul ((hasDerivAt_id' x).sub_const b)).div_const
    (2 : ℝ) using 1
  ring

private theorem trapezoidKernelOne_hasDerivAt (a b x : ℝ) :
    HasDerivAt (trapezoidKernelOne a b) 1 x :=
  (hasDerivAt_id x).sub_const ((a + b) / 2)

private theorem trapezoidKernelPrimitive_hasDerivAt (a b x : ℝ) :
    HasDerivAt (trapezoidKernelPrimitive a b) (trapezoidKernel a b x) x := by
  unfold trapezoidKernelPrimitive trapezoidKernel
  convert ((((hasDerivAt_id' x).sub_const a).pow 3).div_const (6 : ℝ)).sub
    (((((hasDerivAt_id' x).sub_const a).pow 2).const_mul (b - a)).div_const (4 : ℝ)) using 1
  ring

private theorem trapezoidKernel_continuous (a b : ℝ) : Continuous (trapezoidKernel a b) :=
  continuous_iff_continuousAt.mpr fun x ↦ (trapezoidKernel_hasDerivAt a b x).continuousAt

private theorem trapezoidKernel_integral_identity
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) :
    (∫ x in a..b, trapezoidKernel a b x * iteratedDerivWithin 2 f (Icc a b) x) =
      (∫ x in a..b, f x) - trapezoidRule.valueOn f a b := by
  rw [integral_mul_iteratedDerivWithin_two hab subset_rfl (uniqueDiffOn_Icc hab) hf
      (trapezoidKernel_hasDerivAt a b) (trapezoidKernelOne_hasDerivAt a b)
      (continuous_const.intervalIntegrable _ _), trapezoidRule_valueOn_eq_formula]
  norm_num [trapezoidKernel, trapezoidKernelOne]
  ring

private theorem integral_trapezoidKernel {a b : ℝ} :
    (∫ x in a..b, trapezoidKernel a b x) = -(b - a) ^ 3 / 12 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ trapezoidKernelPrimitive_hasDerivAt a b x)
    ((trapezoidKernel_continuous a b).intervalIntegrable _ _)]
  norm_num [trapezoidKernelPrimitive]
  ring

private theorem trapezoidKernel_nonpos {a b x : ℝ} (hx : x ∈ Icc a b) :
    trapezoidKernel a b x ≤ 0 := by
  rw [trapezoidKernel]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2))
    (by norm_num)

/--
Sharp one-panel trapezoid estimate on an ordered interval.

A bound `C` for the second within-derivative yields the classical error `C (b-a)³ / 12`.
-/
theorem norm_integral_sub_trapezoidRule_valueOn_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hsecond : ∀ x ∈ Icc a b, ‖iteratedDerivWithin 2 f (Icc a b) x‖ ≤ C) :
    ‖(∫ x in a..b, f x) - trapezoidRule.valueOn f a b‖ ≤ C * (b - a) ^ 3 / 12 := by
  rw [← trapezoidKernel_integral_identity hab hf]
  refine (norm_integral_mul_le_of_nonpos hab.le (trapezoidKernel_continuous a b)
    (fun _ hx ↦ trapezoidKernel_nonpos hx) hsecond).trans_eq ?_
  rw [integral_trapezoidKernel]
  ring

/-! ### The midpoint kernel -/

private noncomputable def midpointKernelLeft (a x : ℝ) : ℝ :=
  (x - a) ^ 2 / 2

private noncomputable def midpointKernelLeftPrimitive (a x : ℝ) : ℝ :=
  (x - a) ^ 3 / 6

private theorem midpointKernelLeft_hasDerivAt (a x : ℝ) :
    HasDerivAt (midpointKernelLeft a) (x - a) x := by
  unfold midpointKernelLeft
  convert (((hasDerivAt_id' x).sub_const a).pow 2).div_const (2 : ℝ) using 1
  ring

private theorem midpointKernelLeftOne_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun y ↦ y - a) 1 x :=
  (hasDerivAt_id' x).sub_const a

private theorem midpointKernelLeftPrimitive_hasDerivAt (a x : ℝ) :
    HasDerivAt (midpointKernelLeftPrimitive a) (midpointKernelLeft a x) x := by
  unfold midpointKernelLeftPrimitive midpointKernelLeft
  convert (((hasDerivAt_id' x).sub_const a).pow 3).div_const (6 : ℝ) using 1
  ring

private theorem midpointKernelLeft_continuous (a : ℝ) : Continuous (midpointKernelLeft a) :=
  continuous_iff_continuousAt.mpr fun x ↦ (midpointKernelLeft_hasDerivAt a x).continuousAt

private theorem midpointKernelLeft_nonneg (a x : ℝ) : 0 ≤ midpointKernelLeft a x := by
  unfold midpointKernelLeft
  positivity

private theorem integral_midpointKernelLeft (a c : ℝ) :
    (∫ x in c..a, midpointKernelLeft a x) = -(c - a) ^ 3 / 6 ∧
      (∫ x in a..c, midpointKernelLeft a x) = (c - a) ^ 3 / 6 := by
  constructor <;>
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ midpointKernelLeftPrimitive_hasDerivAt a x)
      ((midpointKernelLeft_continuous a).intervalIntegrable _ _)] <;>
    simp only [midpointKernelLeftPrimitive] <;>
    ring

private theorem midpointKernel_integral_identity
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) :
    (∫ x in a..(a + b) / 2, midpointKernelLeft a x * iteratedDerivWithin 2 f (Icc a b) x) +
      (∫ x in (a + b) / 2..b,
        midpointKernelLeft b x * iteratedDerivWithin 2 f (Icc a b) x) =
      (∫ x in a..b, f x) - midpointRule.valueOn f a b := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  have hfL : IntervalIntegrable f volume a ((a + b) / 2) :=
    (hf.continuousOn.mono (Icc_subset_Icc_right hmb.le)).intervalIntegrable_of_Icc ham.le
  have hfR : IntervalIntegrable f volume ((a + b) / 2) b :=
    (hf.continuousOn.mono (Icc_subset_Icc_left ham.le)).intervalIntegrable_of_Icc hmb.le
  rw [integral_mul_iteratedDerivWithin_two ham (Icc_subset_Icc_right hmb.le)
      (uniqueDiffOn_Icc hab) hf (midpointKernelLeft_hasDerivAt a)
      (midpointKernelLeftOne_hasDerivAt a) (continuous_const.intervalIntegrable _ _),
    integral_mul_iteratedDerivWithin_two hmb (Icc_subset_Icc_left ham.le)
      (uniqueDiffOn_Icc hab) hf (midpointKernelLeft_hasDerivAt b)
      (midpointKernelLeftOne_hasDerivAt b) (continuous_const.intervalIntegrable _ _),
    midpointRule_valueOn_eq_formula, ← intervalIntegral.integral_add_adjacent_intervals hfL hfR]
  simp only [midpointKernelLeft, one_mul]
  ring

/--
Sharp one-panel midpoint estimate on an ordered interval.

A bound `C` for the second within-derivative yields the classical error `C (b-a)³ / 24`.
-/
theorem norm_integral_sub_midpointRule_valueOn_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hsecond : ∀ x ∈ Icc a b, ‖iteratedDerivWithin 2 f (Icc a b) x‖ ≤ C) :
    ‖(∫ x in a..b, f x) - midpointRule.valueOn f a b‖ ≤ C * (b - a) ^ 3 / 24 := by
  rw [← midpointKernel_integral_identity hab hf]
  refine (norm_add_le _ _).trans ((add_le_add
    (norm_integral_mul_le_of_nonneg (by linarith) (midpointKernelLeft_continuous a)
      (fun x _ ↦ midpointKernelLeft_nonneg a x) fun x hx ↦ hsecond x ⟨hx.1, by linarith [hx.2]⟩)
    (norm_integral_mul_le_of_nonneg (by linarith) (midpointKernelLeft_continuous b)
      (fun x _ ↦ midpointKernelLeft_nonneg b x)
      fun x hx ↦ hsecond x ⟨by linarith [hx.1], hx.2⟩)).trans_eq ?_)
  rw [(integral_midpointKernelLeft a ((a + b) / 2)).2,
    (integral_midpointKernelLeft b ((a + b) / 2)).1]
  ring

/-- A second-derivative bound gives a midpoint upper bound for the integral.

The derivatives are ordinary derivatives, including at the panel endpoints.
The pointwise `C²` hypothesis converts them to the within-derivatives used by
our midpoint error estimate. -/
theorem integral_le_midpoint_of_second_deriv_bound
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 f x)
    (hsecond : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ C) :
    (∫ x in a..b, f x) ≤
      (b - a) * f ((a + b) / 2) + C * (b - a) ^ 3 / 24 := by
  have h := norm_integral_sub_midpointRule_valueOn_le hab
    (fun x hx ↦ (hf x hx).contDiffWithinAt) (fun x hx ↦ by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (hf x hx) hx,
        Real.norm_eq_abs]
      exact hsecond x hx)
  rw [midpointRule_valueOn_eq_formula, Real.norm_eq_abs] at h
  linarith only [(abs_le.mp h).2]

namespace trapezoidRule

/-- The trapezoidal rule with its sharp one-panel constant `12`. -/
noncomputable def secondOrder : PanelRule 2 where
  rule := trapezoidRule
  denominator := 12
  denominator_pos := by norm_num
  norm_integral_sub_valueOn_le := norm_integral_sub_trapezoidRule_valueOn_le

/-- The underlying normalized rule. -/
@[simp]
theorem secondOrder_rule : secondOrder.rule = trapezoidRule :=
  rfl

/-- The one-panel denominator. -/
@[simp]
theorem secondOrder_denominator : secondOrder.denominator = 12 :=
  rfl

end trapezoidRule

namespace midpointRule

/-- The midpoint rule with its sharp one-panel constant `24`. -/
noncomputable def secondOrder : PanelRule 2 where
  rule := midpointRule
  denominator := 24
  denominator_pos := by norm_num
  norm_integral_sub_valueOn_le := norm_integral_sub_midpointRule_valueOn_le

/-- The underlying normalized rule. -/
@[simp]
theorem secondOrder_rule : secondOrder.rule = midpointRule :=
  rfl

/-- The one-panel denominator. -/
@[simp]
theorem secondOrder_denominator : secondOrder.denominator = 24 :=
  rfl

end midpointRule
end CAS.Continuum
