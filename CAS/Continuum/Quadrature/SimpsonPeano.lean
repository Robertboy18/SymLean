/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.PeanoKernel

/-!
# Simpson quadrature by the Peano kernel

Peano's argument for Simpson's rule on an ordered interval `[a,b]`, with the
classical one-panel bound

`C * (b - a)^5 / 2880`.

For `f ∈ C⁴[a,b]` the Simpson error is `∫ₐᵇ K(x) f⁗(x) dx` with a
piecewise-polynomial kernel `K`, split at the midpoint, that is nonpositive on
`[a,b]` and has total mass `-(b-a)^5/2880` (each half contributes
`-(b-a)^5/5760`, computed here by exact integration). Bounding `|f⁗| ≤ C`
under the integral gives the estimate. Because the kernel has one sign, the bound is attained
by `f(x) = x⁴`; we do not state that sharpness as a theorem. The normalized statements on
`[0,1]` are the case `a = 0`, `b = 1`.

## Main results

* `simpsonRule_valueOn_eq_formula`: the transported rule is the three-node
  formula `(b-a)(f(a) + 4f((a+b)/2) + f(b))/6`.
* `norm_integral_sub_simpsonRule_valueOn_le`: the fourth-order one-panel estimate
  `‖∫ₐᵇ f - S‖ ≤ C (b-a)^5 / 2880` for `f` of class `C⁴` on `[a,b]` with
  `‖f⁗‖ ≤ C` there (in the sense of `iteratedDerivWithin 4 f (Icc a b)`).
* `simpsonRule.fourthOrderCert`: the estimate as a `QuadratureCert`.
* `norm_integral_sub_simpsonRule_valueOn_zero_one_le`, `simpsonRule.fourthOrderCertZeroOne`:
  the normalized estimate `C / 2880` on `[0,1]`.

## Implementation notes

We write the kernel down rather than derive it from Peano's general formula. On the left half it
is the quartic `(x-a)³(3(x-a) - 2(b-a))/72`, on the right half its mirror image in `b`, and
each comes with its chain of three derivatives as polynomials on all of `ℝ`. We apply
`integral_mul_iteratedDerivWithin_four` once on each half; `ring` checks that the boundary terms
add up to the Simpson value, and `norm_integral_mul_le_of_nonpos` bounds each half by its mass.
The two quartics agree with Peano's kernel for this rule (the error functional applied to
`(t-x)₊³/6`), and the constant `2880` is classical; the Lean proof is ours. Every Simpson
certificate in the library (composite, planned, adaptive, batch) rests on
`norm_integral_sub_simpsonRule_valueOn_le`.

## References

* Giuseppe Peano, "Resto nelle formule di quadratura, espresso con un integrale definito",
  *Atti della Reale Accademia dei Lincei, Rendiconti, Classe di scienze fisiche, matematiche e
  naturali*, series 5, 22, first semester (1913), pp. 562-569,
  <https://archive.org/details/rendiconti-lincei_1913-05-04_22_part-1/page/n33/mode/1up>.
  The remainder as an integral of the derivative against a kernel (p. 562).
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equation (3.5.6) gives Simpson's rule with `h = (b-a)/2` and the
  error term `-h⁵f⁽⁴⁾(ξ)/90`, which is `(b-a)⁵/2880` times `f⁽⁴⁾(ξ)`.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

private noncomputable def simpsonKernelLeftOn (a b x : ℝ) : ℝ :=
  (x - a) ^ 3 * (3 * (x - a) - 2 * (b - a)) / 72

private noncomputable def simpsonKernelLeftOnOne (a b x : ℝ) : ℝ :=
  (x - a) ^ 2 * (2 * (x - a) - (b - a)) / 12

private noncomputable def simpsonKernelLeftOnTwo (a b x : ℝ) : ℝ :=
  (x - a) * (3 * (x - a) - (b - a)) / 6

private noncomputable def simpsonKernelLeftOnThree (a b x : ℝ) : ℝ :=
  (x - a) - (b - a) / 6

private noncomputable def simpsonKernelRightOn (a b x : ℝ) : ℝ :=
  (x - b) ^ 3 * (3 * (x - b) + 2 * (b - a)) / 72

private noncomputable def simpsonKernelRightOnOne (a b x : ℝ) : ℝ :=
  (x - b) ^ 2 * (2 * (x - b) + (b - a)) / 12

private noncomputable def simpsonKernelRightOnTwo (a b x : ℝ) : ℝ :=
  (x - b) * (3 * (x - b) + (b - a)) / 6

private noncomputable def simpsonKernelRightOnThree (a b x : ℝ) : ℝ :=
  (x - b) + (b - a) / 6

private theorem simpsonKernelLeftOn_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelLeftOn a b)
      (simpsonKernelLeftOnOne a b x) x := by
  unfold simpsonKernelLeftOn simpsonKernelLeftOnOne
  convert ((((hasDerivAt_id' x).sub_const a).fun_pow 3).mul
    ((((hasDerivAt_id' x).sub_const a).const_mul (3 : ℝ)).sub_const
      (2 * (b - a)))).div_const (72 : ℝ) using 1
  ring

private theorem simpsonKernelLeftOnOne_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelLeftOnOne a b)
      (simpsonKernelLeftOnTwo a b x) x := by
  unfold simpsonKernelLeftOnOne simpsonKernelLeftOnTwo
  convert ((((hasDerivAt_id' x).sub_const a).fun_pow 2).mul
    ((((hasDerivAt_id' x).sub_const a).const_mul (2 : ℝ)).sub_const
      (b - a))).div_const (12 : ℝ) using 1
  ring

private theorem simpsonKernelLeftOnTwo_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelLeftOnTwo a b)
      (simpsonKernelLeftOnThree a b x) x := by
  unfold simpsonKernelLeftOnTwo simpsonKernelLeftOnThree
  convert (((hasDerivAt_id' x).sub_const a).mul
    ((((hasDerivAt_id' x).sub_const a).const_mul (3 : ℝ)).sub_const
      (b - a))).div_const (6 : ℝ) using 1
  ring

private theorem simpsonKernelLeftOnThree_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelLeftOnThree a b) 1 x :=
  (hasDerivAt_id x).sub_const a |>.sub_const ((b - a) / 6)

private theorem simpsonKernelRightOn_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelRightOn a b)
      (simpsonKernelRightOnOne a b x) x := by
  unfold simpsonKernelRightOn simpsonKernelRightOnOne
  convert ((((hasDerivAt_id' x).sub_const b).fun_pow 3).mul
    ((((hasDerivAt_id' x).sub_const b).const_mul (3 : ℝ)).add_const
      (2 * (b - a)))).div_const (72 : ℝ) using 1
  ring

private theorem simpsonKernelRightOnOne_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelRightOnOne a b)
      (simpsonKernelRightOnTwo a b x) x := by
  unfold simpsonKernelRightOnOne simpsonKernelRightOnTwo
  convert ((((hasDerivAt_id' x).sub_const b).fun_pow 2).mul
    ((((hasDerivAt_id' x).sub_const b).const_mul (2 : ℝ)).add_const
      (b - a))).div_const (12 : ℝ) using 1
  ring

private theorem simpsonKernelRightOnTwo_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelRightOnTwo a b)
      (simpsonKernelRightOnThree a b x) x := by
  unfold simpsonKernelRightOnTwo simpsonKernelRightOnThree
  convert (((hasDerivAt_id' x).sub_const b).mul
    ((((hasDerivAt_id' x).sub_const b).const_mul (3 : ℝ)).add_const
      (b - a))).div_const (6 : ℝ) using 1
  ring

private theorem simpsonKernelRightOnThree_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelRightOnThree a b) 1 x :=
  (hasDerivAt_id x).sub_const b |>.add_const ((b - a) / 6)

/-- The transported Simpson value on `[a,b]` is the classical three-node formula
`(b-a) (f a + 4 f((a+b)/2) + f b) / 6`. -/
theorem simpsonRule_valueOn_eq_formula (f : ℝ → ℝ) (a b : ℝ) :
    simpsonRule.valueOn f a b =
      (b - a) * (f a + 4 * f ((a + b) / 2) + f b) / 6 := by
  norm_num [QuadratureRule.valueOn, QuadratureRule.termsOn,
    simpsonRule, weightedSum]
  rw [show a + 1 / 2 * (b - a) = (a + b) / 2 by ring]
  ring

private theorem simpsonKernelOn_integral_identity
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b)) :
    (∫ x in a..(a + b) / 2,
        simpsonKernelLeftOn a b x *
          iteratedDerivWithin 4 f (Icc a b) x) +
      (∫ x in (a + b) / 2..b,
        simpsonKernelRightOn a b x *
          iteratedDerivWithin 4 f (Icc a b) x) =
      (∫ x in a..b, f x) - simpsonRule.valueOn f a b := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  have hfL : IntervalIntegrable f volume a ((a + b) / 2) :=
    (hf.continuousOn.mono (Icc_subset_Icc_right hmb.le)).intervalIntegrable_of_Icc ham.le
  have hfR : IntervalIntegrable f volume ((a + b) / 2) b :=
    (hf.continuousOn.mono (Icc_subset_Icc_left ham.le)).intervalIntegrable_of_Icc hmb.le
  rw [integral_mul_iteratedDerivWithin_four ham (Icc_subset_Icc_right hmb.le)
      (uniqueDiffOn_Icc hab) hf (simpsonKernelLeftOn_hasDerivAt a b)
      (simpsonKernelLeftOnOne_hasDerivAt a b) (simpsonKernelLeftOnTwo_hasDerivAt a b)
      (simpsonKernelLeftOnThree_hasDerivAt a b) (continuous_const.intervalIntegrable _ _),
    integral_mul_iteratedDerivWithin_four hmb (Icc_subset_Icc_left ham.le)
      (uniqueDiffOn_Icc hab) hf (simpsonKernelRightOn_hasDerivAt a b)
      (simpsonKernelRightOnOne_hasDerivAt a b) (simpsonKernelRightOnTwo_hasDerivAt a b)
      (simpsonKernelRightOnThree_hasDerivAt a b) (continuous_const.intervalIntegrable _ _),
    simpsonRule_valueOn_eq_formula, ← intervalIntegral.integral_add_adjacent_intervals hfL hfR]
  simp only [simpsonKernelLeftOn, simpsonKernelLeftOnOne, simpsonKernelLeftOnTwo,
    simpsonKernelLeftOnThree, simpsonKernelRightOn, simpsonKernelRightOnOne,
    simpsonKernelRightOnTwo, simpsonKernelRightOnThree, one_mul]
  ring

private noncomputable def simpsonKernelLeftOnPrimitive (a b x : ℝ) : ℝ :=
  (x - a) ^ 5 / 120 - (b - a) * (x - a) ^ 4 / 144

private noncomputable def simpsonKernelRightOnPrimitive (a b x : ℝ) : ℝ :=
  (x - b) ^ 5 / 120 + (b - a) * (x - b) ^ 4 / 144

private theorem simpsonKernelLeftOnPrimitive_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelLeftOnPrimitive a b)
      (simpsonKernelLeftOn a b x) x := by
  unfold simpsonKernelLeftOnPrimitive simpsonKernelLeftOn
  convert ((((hasDerivAt_id' x).sub_const a).pow 5).div_const (120 : ℝ)).sub
    (((((hasDerivAt_id' x).sub_const a).pow 4).const_mul (b - a)).div_const (144 : ℝ)) using 1
  ring

private theorem simpsonKernelRightOnPrimitive_hasDerivAt (a b x : ℝ) :
    HasDerivAt (simpsonKernelRightOnPrimitive a b)
      (simpsonKernelRightOn a b x) x := by
  unfold simpsonKernelRightOnPrimitive simpsonKernelRightOn
  convert ((((hasDerivAt_id' x).sub_const b).pow 5).div_const (120 : ℝ)).add
    (((((hasDerivAt_id' x).sub_const b).pow 4).const_mul (b - a)).div_const (144 : ℝ)) using 1
  ring

private theorem integral_simpsonKernelLeftOn
    {a b : ℝ} :
    (∫ x in a..(a + b) / 2, simpsonKernelLeftOn a b x) =
      -(b - a) ^ 5 / 5760 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ simpsonKernelLeftOnPrimitive_hasDerivAt a b x)
    ((continuous_iff_continuousAt.mpr fun x ↦
      (simpsonKernelLeftOn_hasDerivAt a b x).continuousAt).intervalIntegrable _ _)]
  unfold simpsonKernelLeftOnPrimitive
  ring

private theorem integral_simpsonKernelRightOn
    {a b : ℝ} :
    (∫ x in (a + b) / 2..b, simpsonKernelRightOn a b x) =
      -(b - a) ^ 5 / 5760 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ simpsonKernelRightOnPrimitive_hasDerivAt a b x)
    ((continuous_iff_continuousAt.mpr fun x ↦
      (simpsonKernelRightOn_hasDerivAt a b x).continuousAt).intervalIntegrable _ _)]
  unfold simpsonKernelRightOnPrimitive
  ring

private theorem simpsonKernelLeftOn_nonpos
    {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Icc a ((a + b) / 2)) :
    simpsonKernelLeftOn a b x ≤ 0 := by
  rw [simpsonKernelLeftOn]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
    (pow_nonneg (sub_nonneg.2 hx.1) 3) (by linarith [hx.2])) (by norm_num)

private theorem simpsonKernelRightOn_nonpos
    {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Icc ((a + b) / 2) b) :
    simpsonKernelRightOn a b x ≤ 0 := by
  rw [simpsonKernelRightOn]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
    (Odd.pow_nonpos ⟨1, rfl⟩ (sub_nonpos.2 hx.2)) (by linarith [hx.1])) (by norm_num)

private theorem norm_integral_simpsonKernelLeftOn_mul_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    ‖∫ x in a..(a + b) / 2,
        simpsonKernelLeftOn a b x *
          iteratedDerivWithin 4 f (Icc a b) x‖ ≤
      (b - a) ^ 5 / 5760 * C := by
  refine (norm_integral_mul_le_of_nonpos (by linarith)
    (continuous_iff_continuousAt.mpr fun x ↦ (simpsonKernelLeftOn_hasDerivAt a b x).continuousAt)
    (fun x hx ↦ simpsonKernelLeftOn_nonpos hab.le hx)
    fun x hx ↦ hfourth x ⟨hx.1, by linarith [hx.2]⟩).trans_eq ?_
  rw [integral_simpsonKernelLeftOn]
  ring

private theorem norm_integral_simpsonKernelRightOn_mul_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    ‖∫ x in (a + b) / 2..b,
        simpsonKernelRightOn a b x *
          iteratedDerivWithin 4 f (Icc a b) x‖ ≤
      (b - a) ^ 5 / 5760 * C := by
  refine (norm_integral_mul_le_of_nonpos (by linarith)
    (continuous_iff_continuousAt.mpr fun x ↦ (simpsonKernelRightOn_hasDerivAt a b x).continuousAt)
    (fun x hx ↦ simpsonKernelRightOn_nonpos hab.le hx)
    fun x hx ↦ hfourth x ⟨by linarith [hx.1], hx.2⟩).trans_eq ?_
  rw [integral_simpsonKernelRightOn]
  ring

/--
Sharp one-panel Simpson estimate on an ordered interval.

The fourth within-derivative bound `C` yields the classical error
`C * (b-a)^5 / 2880`.
-/
theorem norm_integral_sub_simpsonRule_valueOn_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    ‖(∫ x in a..b, f x) - simpsonRule.valueOn f a b‖ ≤
      C * (b - a) ^ 5 / 2880 := by
  rw [← simpsonKernelOn_integral_identity hab hf]
  refine (norm_add_le _ _).trans ((add_le_add (norm_integral_simpsonKernelLeftOn_mul_le hab hfourth)
    (norm_integral_simpsonKernelRightOn_mul_le hab hfourth)).trans_eq ?_)
  ring

namespace simpsonRule

/-- Sharp one-panel Simpson certificate on an ordered interval. -/
noncomputable def fourthOrderCert
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    QuadratureCert f a b :=
  QuadratureCert.ofErrorBound
    (simpsonRule.valueOn f a b)
    (C * (b - a) ^ 5 / 2880)
    (norm_integral_sub_simpsonRule_valueOn_le hab hf hfourth)

/-- The sharp one-panel certificate stores Simpson's value on `[a,b]`. -/
@[simp]
theorem fourthOrderCert_value
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    (fourthOrderCert hab hf hfourth).value = simpsonRule.valueOn f a b :=
  rfl

/-- The sharp one-panel certificate stores exactly the Peano-kernel error `C (b-a)^5 / 2880`. -/
@[simp]
theorem fourthOrderCert_error
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    (fourthOrderCert hab hf hfourth).error =
      C * (b - a) ^ 5 / 2880 :=
  rfl

end simpsonRule

/-! ### The normalized interval `[0,1]` -/

/--
Sharp normalized Simpson estimate.

If `f` is four-times continuously differentiable on `[0,1]` and its fourth
within-derivative has norm at most `C`, then one Simpson panel has error at
most `C / 2880`. This is `norm_integral_sub_simpsonRule_valueOn_le` on `[0,1]`.
-/
theorem norm_integral_sub_simpsonRule_valueOn_zero_one_le
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc (0 : ℝ) 1))
    (hfourth : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x‖ ≤ C) :
    ‖(∫ x in (0 : ℝ)..1, f x) - simpsonRule.valueOn f 0 1‖ ≤
      C / 2880 := by
  simpa using norm_integral_sub_simpsonRule_valueOn_le one_pos hf hfourth

namespace simpsonRule

/--
Checked sharp Simpson certificate on the normalized interval `[0,1]`.

This constructor uses the exact Peano-kernel constant and stores only the
classical analytic error `C / 2880`.
-/
noncomputable def fourthOrderCertZeroOne
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc (0 : ℝ) 1))
    (hfourth : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x‖ ≤ C) :
    QuadratureCert f 0 1 :=
  QuadratureCert.ofErrorBound
    (simpsonRule.valueOn f 0 1) (C / 2880)
    (norm_integral_sub_simpsonRule_valueOn_zero_one_le hf hfourth)

/-- The sharp normalized certificate stores Simpson's three-node value
`(f 0 + 4 f(1/2) + f 1) / 6`. -/
@[simp]
theorem fourthOrderCertZeroOne_value
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc (0 : ℝ) 1))
    (hfourth : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x‖ ≤ C) :
    (fourthOrderCertZeroOne hf hfourth).value =
      simpsonRule.valueOn f 0 1 :=
  rfl

/-- The sharp normalized certificate stores exactly the Peano-kernel error `C / 2880`. -/
@[simp]
theorem fourthOrderCertZeroOne_error
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc (0 : ℝ) 1))
    (hfourth : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x‖ ≤ C) :
    (fourthOrderCertZeroOne hf hfourth).error = C / 2880 :=
  rfl

end simpsonRule

end CAS.Continuum
