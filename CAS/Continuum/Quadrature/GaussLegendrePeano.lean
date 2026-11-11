/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.GaussLegendre
public import CAS.Continuum.Quadrature.PeanoKernel

/-!
# Peano remainder for two-point Gauss-Legendre quadrature

The two-point Gauss-Legendre rule is exact through degree three.  Its
fourth-derivative error estimate holds on every ordered interval:

`‖∫_a^b f - Q₂(f)‖ ≤ C * (b - a)^5 / 4320`.

The constant agrees with the remainder `f⁗(ξ)/135` of the two-point rule on `[-1,1]`, since
`2^5 · 135 = 4320`.

## Main results

* `gaussLegendreTwoRule_valueOn_eq_formula`: the transported rule is
  `(b-a)/2 · (f(x₋) + f(x₊))` at the two Gauss nodes.
* `norm_integral_sub_gaussLegendreTwoRule_valueOn_le`: the fourth-order one-panel
  estimate `‖∫ₐᵇ f - Q₂(f)‖ ≤ C (b-a)^5 / 4320` for `f ∈ C⁴[a,b]` with
  `‖f⁗‖ ≤ C` on `[a,b]` (as `iteratedDerivWithin 4 f (Icc a b)`).
* `gaussLegendreTwoRule.fourthOrderCert`: the estimate as a `QuadratureCert`.

## Implementation notes

We write the Peano kernel out on its three pieces, split at the two Gauss nodes, with its first
three derivatives, and `integral_mul_iteratedDerivWithin_four` of `PeanoKernel` integrates by
parts four times on each piece (`gaussKernel_integral_identity`). The outer pieces are
`(x - a)^4 / 24` and `(x - b)^4 / 24`. The middle piece is `(s^2 + (b - a)^4 c) / 24` for an
explicit quadratic `s` and `c = -5/4 + 13√3/18 ≈ 9.3e-4 > 0`
(`gaussKernelMiddle_sum_of_squares`). Exact integration of the three polynomial pieces gives the
kernel mass `(b - a)^5 / 4320` (`gaussKernel_total_mass`), and the error is at most `C` times
the mass. The kernel has one sign, so equality holds for `f(x) = x⁴`; this is not proved here.

## References

* Giuseppe Peano, "Resto nelle formule di quadratura, espresso con un integrale definito",
  *Atti della Reale Accademia dei Lincei, Rendiconti, Classe di scienze fisiche, matematiche e
  naturali*, series 5, 22, first semester (1913), pp. 562-569,
  <https://archive.org/details/rendiconti-lincei_1913-05-04_22_part-1/page/n33/mode/1up>.
* Walter Gautschi, *Numerical Analysis*, 2nd ed., Birkhäuser, Boston, 2012,
  <https://doi.org/10.1007/978-0-8176-8259-0>.
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. (3.5.19) and (3.5.21), with `n = 2`, for the remainder
  `f⁗(ξ)/135` on `[-1, 1]`.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- Left Gauss node transported to `[a,b]`. -/
noncomputable def gaussLegendreTwoLeftPoint (a b : ℝ) : ℝ :=
  a + gaussLegendreTwoLeftNode * (b - a)

/-- Right Gauss node transported to `[a,b]`. -/
noncomputable def gaussLegendreTwoRightPoint (a b : ℝ) : ℝ :=
  a + gaussLegendreTwoRightNode * (b - a)

/-- On a nondegenerate interval the two transported Gauss nodes are in increasing order, since
`(3 - √3)/6 < (3 + √3)/6`. -/
theorem gaussLegendreTwoLeftPoint_lt_rightPoint
    {a b : ℝ} (hab : a < b) :
    gaussLegendreTwoLeftPoint a b <
      gaussLegendreTwoRightPoint a b := by
  unfold gaussLegendreTwoLeftPoint gaussLegendreTwoRightPoint
    gaussLegendreTwoLeftNode gaussLegendreTwoRightNode
  nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]

/-- The transported left Gauss node lies in `[a, b]` whenever `a ≤ b`. -/
theorem gaussLegendreTwoLeftPoint_mem_Icc
    {a b : ℝ} (hab : a ≤ b) :
    gaussLegendreTwoLeftPoint a b ∈ Icc a b := by
  have h := gaussLegendreTwoLeftNode_mem_unit
  unfold gaussLegendreTwoLeftPoint
  constructor <;> nlinarith [h.1, h.2]

/-- The transported right Gauss node lies in `[a, b]` whenever `a ≤ b`. -/
theorem gaussLegendreTwoRightPoint_mem_Icc
    {a b : ℝ} (hab : a ≤ b) :
    gaussLegendreTwoRightPoint a b ∈ Icc a b := by
  have h := gaussLegendreTwoRightNode_mem_unit
  unfold gaussLegendreTwoRightPoint
  constructor <;> nlinarith [h.1, h.2]

/-- The transported two-point Gauss rule is the average of `f` at the two Gauss nodes times the
interval length: `(b-a)/2 · (f(x₋) + f(x₊))` with `x∓ = a + (3 ∓ √3)/6 · (b-a)`. -/
theorem gaussLegendreTwoRule_valueOn_eq_formula
    (f : ℝ → ℝ) (a b : ℝ) :
    gaussLegendreTwoRule.valueOn f a b =
      (b - a) / 2 *
        (f (gaussLegendreTwoLeftPoint a b) +
          f (gaussLegendreTwoRightPoint a b)) := by
  norm_num [QuadratureRule.valueOn, QuadratureRule.termsOn,
    gaussLegendreTwoRule, gaussLegendreTwoLeftPoint,
    gaussLegendreTwoRightPoint, weightedSum]
  ring

private noncomputable def gaussKernelLeft (a x : ℝ) : ℝ :=
  (x - a) ^ 4 / 24

private noncomputable def gaussKernelLeftOne (a x : ℝ) : ℝ :=
  (x - a) ^ 3 / 6

private noncomputable def gaussKernelLeftTwo (a x : ℝ) : ℝ :=
  (x - a) ^ 2 / 2

private noncomputable def gaussKernelLeftThree (a x : ℝ) : ℝ :=
  x - a

private noncomputable def gaussKernelMiddle (a b x : ℝ) : ℝ :=
  (x - b) ^ 4 / 24 -
    (b - a) * (gaussLegendreTwoRightPoint a b - x) ^ 3 / 12

private noncomputable def gaussKernelMiddleOne (a b x : ℝ) : ℝ :=
  (x - b) ^ 3 / 6 +
    (b - a) * (gaussLegendreTwoRightPoint a b - x) ^ 2 / 4

private noncomputable def gaussKernelMiddleTwo (a b x : ℝ) : ℝ :=
  (x - b) ^ 2 / 2 -
    (b - a) * (gaussLegendreTwoRightPoint a b - x) / 2

private noncomputable def gaussKernelMiddleThree (a b x : ℝ) : ℝ :=
  x - (a + b) / 2

private noncomputable def gaussKernelRight (b x : ℝ) : ℝ :=
  (x - b) ^ 4 / 24

private noncomputable def gaussKernelRightOne (b x : ℝ) : ℝ :=
  (x - b) ^ 3 / 6

private noncomputable def gaussKernelRightTwo (b x : ℝ) : ℝ :=
  (x - b) ^ 2 / 2

private noncomputable def gaussKernelRightThree (b x : ℝ) : ℝ :=
  x - b

private theorem gaussKernelLeft_hasDerivAt (a x : ℝ) :
    HasDerivAt (gaussKernelLeft a) (gaussKernelLeftOne a x) x := by
  unfold gaussKernelLeft gaussKernelLeftOne
  convert (((hasDerivAt_id' x).sub_const a).pow 4).div_const (24 : ℝ) using 1
  ring

private theorem gaussKernelLeftOne_hasDerivAt (a x : ℝ) :
    HasDerivAt (gaussKernelLeftOne a) (gaussKernelLeftTwo a x) x := by
  unfold gaussKernelLeftOne gaussKernelLeftTwo
  convert (((hasDerivAt_id' x).sub_const a).pow 3).div_const (6 : ℝ) using 1
  ring

private theorem gaussKernelLeftTwo_hasDerivAt (a x : ℝ) :
    HasDerivAt (gaussKernelLeftTwo a) (gaussKernelLeftThree a x) x := by
  unfold gaussKernelLeftTwo gaussKernelLeftThree
  convert (((hasDerivAt_id' x).sub_const a).pow 2).div_const (2 : ℝ) using 1
  ring

private theorem gaussKernelLeftThree_hasDerivAt (a x : ℝ) :
    HasDerivAt (gaussKernelLeftThree a) 1 x :=
  (hasDerivAt_id x).sub_const a

private theorem gaussKernelMiddle_hasDerivAt (a b x : ℝ) :
    HasDerivAt (gaussKernelMiddle a b)
      (gaussKernelMiddleOne a b x) x := by
  unfold gaussKernelMiddle gaussKernelMiddleOne
  convert ((((hasDerivAt_id' x).sub_const b).pow 4).div_const (24 : ℝ)).sub
    (((((hasDerivAt_id' x).const_sub
      (gaussLegendreTwoRightPoint a b)).pow 3).const_mul (b - a)).div_const (12 : ℝ)) using 1
  ring

private theorem gaussKernelMiddleOne_hasDerivAt (a b x : ℝ) :
    HasDerivAt (gaussKernelMiddleOne a b)
      (gaussKernelMiddleTwo a b x) x := by
  unfold gaussKernelMiddleOne gaussKernelMiddleTwo
  convert ((((hasDerivAt_id' x).sub_const b).pow 3).div_const (6 : ℝ)).add
    (((((hasDerivAt_id' x).const_sub
      (gaussLegendreTwoRightPoint a b)).pow 2).const_mul (b - a)).div_const (4 : ℝ)) using 1
  ring

private theorem gaussKernelMiddleTwo_hasDerivAt (a b x : ℝ) :
    HasDerivAt (gaussKernelMiddleTwo a b)
      (gaussKernelMiddleThree a b x) x := by
  unfold gaussKernelMiddleTwo gaussKernelMiddleThree
  convert ((((hasDerivAt_id' x).sub_const b).pow 2).div_const (2 : ℝ)).sub
    ((((hasDerivAt_id' x).const_sub
      (gaussLegendreTwoRightPoint a b)).const_mul (b - a)).div_const (2 : ℝ)) using 1
  ring

private theorem gaussKernelMiddleThree_hasDerivAt (a b x : ℝ) :
    HasDerivAt (gaussKernelMiddleThree a b) 1 x :=
  (hasDerivAt_id x).sub_const ((a + b) / 2)

private theorem gaussKernelRight_hasDerivAt (b x : ℝ) :
    HasDerivAt (gaussKernelRight b) (gaussKernelRightOne b x) x :=
  gaussKernelLeft_hasDerivAt b x

private theorem gaussKernelRightOne_hasDerivAt (b x : ℝ) :
    HasDerivAt (gaussKernelRightOne b) (gaussKernelRightTwo b x) x :=
  gaussKernelLeftOne_hasDerivAt b x

private theorem gaussKernelRightTwo_hasDerivAt (b x : ℝ) :
    HasDerivAt (gaussKernelRightTwo b) (gaussKernelRightThree b x) x :=
  gaussKernelLeftTwo_hasDerivAt b x

private theorem gaussKernelRightThree_hasDerivAt (b x : ℝ) :
    HasDerivAt (gaussKernelRightThree b) 1 x :=
  (hasDerivAt_id x).sub_const b

private theorem gaussKernel_integral_identity
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b)) :
    (∫ x in a..gaussLegendreTwoLeftPoint a b,
        gaussKernelLeft a x *
          iteratedDerivWithin 4 f (Icc a b) x) +
      (∫ x in gaussLegendreTwoLeftPoint a b..
          gaussLegendreTwoRightPoint a b,
        gaussKernelMiddle a b x *
          iteratedDerivWithin 4 f (Icc a b) x) +
      (∫ x in gaussLegendreTwoRightPoint a b..b,
        gaussKernelRight b x *
          iteratedDerivWithin 4 f (Icc a b) x) =
      (∫ x in a..b, f x) - gaussLegendreTwoRule.valueOn f a b := by
  have h3 : Real.sqrt 3 < 3 := by nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]
  have hal : a < gaussLegendreTwoLeftPoint a b := by
    unfold gaussLegendreTwoLeftPoint gaussLegendreTwoLeftNode
    nlinarith
  have hlr := gaussLegendreTwoLeftPoint_lt_rightPoint hab
  have hrb : gaussLegendreTwoRightPoint a b < b := by
    unfold gaussLegendreTwoRightPoint gaussLegendreTwoRightNode
    nlinarith
  have hsL : Icc a (gaussLegendreTwoLeftPoint a b) ⊆ Icc a b :=
    Icc_subset_Icc_right (hlr.trans hrb).le
  have hsM : Icc (gaussLegendreTwoLeftPoint a b) (gaussLegendreTwoRightPoint a b) ⊆ Icc a b :=
    Icc_subset_Icc hal.le hrb.le
  have hsR : Icc (gaussLegendreTwoRightPoint a b) b ⊆ Icc a b :=
    Icc_subset_Icc_left (hal.trans hlr).le
  have hfi {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
      IntervalIntegrable f volume u v :=
    (hf.continuousOn.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  /-
  Splitting at the two Gauss nodes isolates the jumps in the third kernel
  derivative. After four integrations by parts, those jumps produce the two
  quadrature evaluations, while the outer boundary terms produce the
  interval integral. Only the jumps at the left node need `√3 ^ 2 = 3`.
  -/
  have h0 : gaussKernelLeft a (gaussLegendreTwoLeftPoint a b) =
      gaussKernelMiddle a b (gaussLegendreTwoLeftPoint a b) := by
    unfold gaussKernelLeft gaussKernelMiddle gaussLegendreTwoLeftPoint
      gaussLegendreTwoRightPoint gaussLegendreTwoLeftNode gaussLegendreTwoRightNode
    linear_combination (b - a) ^ 4 * Real.sqrt 3 / 432 * sqrt_three_sq
  have h1 : gaussKernelLeftOne a (gaussLegendreTwoLeftPoint a b) =
      gaussKernelMiddleOne a b (gaussLegendreTwoLeftPoint a b) := by
    unfold gaussKernelLeftOne gaussKernelMiddleOne gaussLegendreTwoLeftPoint
      gaussLegendreTwoRightPoint gaussLegendreTwoLeftNode gaussLegendreTwoRightNode
    linear_combination -(b - a) ^ 3 / 72 * sqrt_three_sq
  have h2 : gaussKernelLeftTwo a (gaussLegendreTwoLeftPoint a b) =
      gaussKernelMiddleTwo a b (gaussLegendreTwoLeftPoint a b) := by
    unfold gaussKernelLeftTwo gaussKernelMiddleTwo gaussLegendreTwoLeftPoint
      gaussLegendreTwoRightPoint gaussLegendreTwoLeftNode gaussLegendreTwoRightNode
    ring
  rw [integral_mul_iteratedDerivWithin_four hal hsL (uniqueDiffOn_Icc hab) hf
      (gaussKernelLeft_hasDerivAt a) (gaussKernelLeftOne_hasDerivAt a)
      (gaussKernelLeftTwo_hasDerivAt a) (gaussKernelLeftThree_hasDerivAt a)
      (continuous_const.intervalIntegrable _ _),
    integral_mul_iteratedDerivWithin_four hlr hsM (uniqueDiffOn_Icc hab) hf
      (gaussKernelMiddle_hasDerivAt a b) (gaussKernelMiddleOne_hasDerivAt a b)
      (gaussKernelMiddleTwo_hasDerivAt a b) (gaussKernelMiddleThree_hasDerivAt a b)
      (continuous_const.intervalIntegrable _ _),
    integral_mul_iteratedDerivWithin_four hrb hsR (uniqueDiffOn_Icc hab) hf
      (gaussKernelRight_hasDerivAt b) (gaussKernelRightOne_hasDerivAt b)
      (gaussKernelRightTwo_hasDerivAt b) (gaussKernelRightThree_hasDerivAt b)
      (continuous_const.intervalIntegrable _ _),
    h0, h1, h2, gaussLegendreTwoRule_valueOn_eq_formula,
    ← intervalIntegral.integral_add_adjacent_intervals (hfi le_rfl (hal.trans hlr).le hrb.le)
      (hfi (hal.trans hlr).le hrb.le le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hfi le_rfl hal.le (hlr.trans hrb).le)
      (hfi hal.le hlr.le hrb.le)]
  simp only [gaussKernelLeft, gaussKernelLeftOne, gaussKernelLeftTwo, gaussKernelLeftThree,
    gaussKernelMiddle, gaussKernelMiddleOne, gaussKernelMiddleTwo, gaussKernelMiddleThree,
    gaussKernelRight, gaussKernelRightOne, gaussKernelRightTwo, gaussKernelRightThree, one_mul]
  ring

private noncomputable def gaussKernelLeftPrimitive (a x : ℝ) : ℝ :=
  (x - a) ^ 5 / 120

private noncomputable def gaussKernelMiddlePrimitive (a b x : ℝ) : ℝ :=
  (x - b) ^ 5 / 120 +
    (b - a) * (gaussLegendreTwoRightPoint a b - x) ^ 4 / 48

private noncomputable def gaussKernelRightPrimitive (b x : ℝ) : ℝ :=
  (x - b) ^ 5 / 120

private theorem gaussKernelLeftPrimitive_hasDerivAt (a x : ℝ) :
    HasDerivAt (gaussKernelLeftPrimitive a) (gaussKernelLeft a x) x := by
  unfold gaussKernelLeftPrimitive gaussKernelLeft
  convert (((hasDerivAt_id' x).sub_const a).pow 5).div_const (120 : ℝ) using 1
  ring

private theorem gaussKernelMiddlePrimitive_hasDerivAt (a b x : ℝ) :
    HasDerivAt (gaussKernelMiddlePrimitive a b)
      (gaussKernelMiddle a b x) x := by
  unfold gaussKernelMiddlePrimitive gaussKernelMiddle
  convert ((((hasDerivAt_id' x).sub_const b).pow 5).div_const (120 : ℝ)).add
    (((((hasDerivAt_id' x).const_sub
      (gaussLegendreTwoRightPoint a b)).pow 4).const_mul (b - a)).div_const (48 : ℝ)) using 1
  ring

private theorem gaussKernelRightPrimitive_hasDerivAt (b x : ℝ) :
    HasDerivAt (gaussKernelRightPrimitive b) (gaussKernelRight b x) x :=
  gaussKernelLeftPrimitive_hasDerivAt b x

/--
Exact total mass of the three Peano-kernel pieces.

The constant `1/4320` is obtained by evaluating the three explicit polynomial
primitives at the Gauss nodes and simplifying `sqrt(3)^2 = 3`.
-/
private theorem gaussKernel_total_mass
    {a b : ℝ} :
    (∫ x in a..gaussLegendreTwoLeftPoint a b, gaussKernelLeft a x) +
      (∫ x in gaussLegendreTwoLeftPoint a b..
          gaussLegendreTwoRightPoint a b, gaussKernelMiddle a b x) +
      (∫ x in gaussLegendreTwoRightPoint a b..b, gaussKernelRight b x) =
        (b - a) ^ 5 / 4320 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ gaussKernelLeftPrimitive_hasDerivAt a x)
      ((continuous_iff_continuousAt.mpr fun x ↦
        (gaussKernelLeft_hasDerivAt a x).continuousAt).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ gaussKernelMiddlePrimitive_hasDerivAt a b x)
      ((continuous_iff_continuousAt.mpr fun x ↦
        (gaussKernelMiddle_hasDerivAt a b x).continuousAt).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ gaussKernelRightPrimitive_hasDerivAt b x)
      ((continuous_iff_continuousAt.mpr fun x ↦
        (gaussKernelRight_hasDerivAt b x).continuousAt).intervalIntegrable _ _)]
  unfold gaussKernelLeftPrimitive gaussKernelMiddlePrimitive gaussKernelRightPrimitive
    gaussLegendreTwoLeftPoint gaussLegendreTwoRightPoint gaussLegendreTwoLeftNode
    gaussLegendreTwoRightNode
  linear_combination -(b - a) ^ 5 * (7 * Real.sqrt 3 ^ 2 + 3) / 31104 * sqrt_three_sq

/--
Algebraic sum-of-squares decomposition used to prove that the middle kernel
piece is nonnegative.
-/
private theorem gaussKernelMiddle_sum_of_squares (a b x : ℝ) :
    gaussKernelMiddle a b x =
      (((x - (a + b) / 2) ^ 2 +
          (b - a) ^ 2 * (3 / 2 - Real.sqrt 3) / 2) ^ 2 +
        (b - a) ^ 4 * (-5 / 4 + 13 * Real.sqrt 3 / 18)) / 24 := by
  unfold gaussKernelMiddle gaussLegendreTwoRightPoint gaussLegendreTwoRightNode
  linear_combination
    (b - a) ^ 3 * (18 * x + 18 * a - 36 * b + (a - b) * Real.sqrt 3) / 2592 * sqrt_three_sq

private theorem gaussKernelLeft_nonneg (a x : ℝ) :
    0 ≤ gaussKernelLeft a x := by
  unfold gaussKernelLeft
  positivity

private theorem gaussKernelMiddle_nonneg (a b x : ℝ) :
    0 ≤ gaussKernelMiddle a b x := by
  rw [gaussKernelMiddle_sum_of_squares]
  -- The margin is small: -5/4 + 13*sqrt 3/18 ≈ 9.3e-4. Perturbing the
  -- decomposition constants can flip the sign.
  have hconstant : 0 ≤ -5 / 4 + 13 * Real.sqrt 3 / 18 := by
    nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]
  positivity

private theorem gaussKernelRight_nonneg (b x : ℝ) :
    0 ≤ gaussKernelRight b x :=
  gaussKernelLeft_nonneg b x

/--
Sharp two-point Gauss-Legendre estimate on an ordered interval.

The fourth within-derivative bound `C` yields the classical error
`C * (b-a)^5 / 4320`. This proof combines the three nonnegative-kernel bounds
with the exact total-mass theorem above.
-/
theorem norm_integral_sub_gaussLegendreTwoRule_valueOn_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    ‖(∫ x in a..b, f x) - gaussLegendreTwoRule.valueOn f a b‖ ≤
      C * (b - a) ^ 5 / 4320 := by
  have hl := gaussLegendreTwoLeftPoint_mem_Icc hab.le
  have hr := gaussLegendreTwoRightPoint_mem_Icc hab.le
  rw [← gaussKernel_integral_identity hab hf]
  refine (norm_add₃_le.trans (add_le_add_three
    (norm_integral_mul_le_of_nonneg hl.1
      (continuous_iff_continuousAt.mpr fun x ↦ (gaussKernelLeft_hasDerivAt a x).continuousAt)
      (fun x _ ↦ gaussKernelLeft_nonneg a x) fun x hx ↦ hfourth x ⟨hx.1, hx.2.trans hl.2⟩)
    (norm_integral_mul_le_of_nonneg (gaussLegendreTwoLeftPoint_lt_rightPoint hab).le
      (continuous_iff_continuousAt.mpr fun x ↦ (gaussKernelMiddle_hasDerivAt a b x).continuousAt)
      (fun x _ ↦ gaussKernelMiddle_nonneg a b x)
      fun x hx ↦ hfourth x ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩)
    (norm_integral_mul_le_of_nonneg hr.2
      (continuous_iff_continuousAt.mpr fun x ↦ (gaussKernelRight_hasDerivAt b x).continuousAt)
      (fun x _ ↦ gaussKernelRight_nonneg b x) fun x hx ↦ hfourth x ⟨hr.1.trans hx.1, hx.2⟩)))
    |>.trans_eq ?_
  linear_combination C * gaussKernel_total_mass (a := a) (b := b)

namespace gaussLegendreTwoRule

/-- Sharp two-point Gauss-Legendre certificate on an ordered interval. -/
noncomputable def fourthOrderCert
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    QuadratureCert f a b :=
  QuadratureCert.ofErrorBound
    (gaussLegendreTwoRule.valueOn f a b)
    (C * (b - a) ^ 5 / 4320)
    (norm_integral_sub_gaussLegendreTwoRule_valueOn_le hab hf hfourth)

/-- The fourth-order certificate stores the two-point Gauss-Legendre value on `[a,b]`. -/
@[simp]
theorem fourthOrderCert_value
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    (fourthOrderCert hab hf hfourth).value =
      gaussLegendreTwoRule.valueOn f a b :=
  rfl

/-- The fourth-order certificate stores exactly the Peano-kernel error `C (b-a)^5 / 4320`. -/
@[simp]
theorem fourthOrderCert_error
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hfourth : ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ C) :
    (fourthOrderCert hab hf hfourth).error =
      C * (b - a) ^ 5 / 4320 :=
  rfl

end gaussLegendreTwoRule
end CAS.Continuum
