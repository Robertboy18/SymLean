/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Trapezoidal
public import CAS.Continuum.Quadrature.Core
public import CAS.Continuum.Quadrature.PanelRule

/-!
# Tolerance-driven quadrature planning

A requested positive error tolerance determines a certified mesh size for
composite trapezoidal quadrature.  The planner is checked:
given a nonnegative bound `ζ` for the absolute second derivative, it chooses

`N = max 1 ⌈(B / tolerance)^(1/2)⌉₊`,

where `B = |b - a|^3 * ζ / 12`.  Consequently the standard trapezoidal error
bound `B / N^2` is at most the requested tolerance.  The planner is the order-`2` case of
`PanelPlan` with denominator `12`, on the endpoints in increasing order.

The planner concerns exact analytic truncation error.  A numerical backend may
subsequently replace the exact-real quadrature value using
`QuadratureCert.replaceValueOfInterval`, adding its certified roundoff budget.

## Main results

* `TrapezoidalPlan.requiredIntervals`, `TrapezoidalPlan.trapezoidalError_le`: the
  mesh size and the proof that `|b-a|^3 ζ / (12 N^2) ≤ tolerance`.
* `QuadratureCert.trapezoidalToTolerance_sound_le`: for `f ∈ C²` on `[a,b]` with
  `|f''| ≤ ζ`, the planned composite trapezoidal value is within the tolerance of
  `∫ₐᵇ f`.
* `QuadratureCert.trapezoidalToTotalToleranceOfInterval_sound_le`: the same with
  a single total budget split between analytic truncation and the radius of a
  verified interval enclosure of the computed value.

## Implementation notes

The planner is arithmetic on reals and proposes nothing that needs checking:
`requiredIntervals` is `PanelPlan.requiredPanels 2 12` on `min a b` and `max a b`, and
`trapezoidalError_le` is `PanelPlan.uniformCompositeError_le` rewritten with
`max a b - min a b = |b - a|`. The certificate is `QuadratureCert.trapezoidal` with the planned
`N`, so the analytic bound is Mathlib's `trapezoidal_error_le_of_c2`, not the Peano-kernel
estimate of `trapezoidRule.secondOrder`. Its value is the exact real `trapezoidal_integral`. A
backend that evaluates it numerically encloses it in an interval `I`;
`trapezoidalToTotalToleranceOfInterval` plans the mesh for the budget `tolerance - radius I` and
then charges `radius I` for replacing the value by the centre of `I`.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020,
  pp. 367-381, <https://doi.org/10.1145/3372885.3373824>. The composite rule
  `trapezoidal_integral` and its error bound `trapezoidal_error_le_of_c2`, which states
  `|∫ₐᵇ f - T_N(f)| ≤ |b-a|³ ζ / (12 N²)` for `f ∈ C²` with `|f''| ≤ ζ`.
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equations (3.5.2) and (3.5.3) give the composite trapezoidal rule
  with the error `-((b-a)/12) h² f''(ξ)`, `h = (b-a)/N`.
-/

@[expose] public section

open Set

namespace CAS.Continuum

namespace TrapezoidalPlan

/-- The interval- and derivative-dependent numerator `|b - a|^3 ζ / 12` of the error bound. -/
noncomputable def errorConstant (a b ζ : ℝ) : ℝ :=
  PanelPlan.errorConstant 2 12 (min a b) (max a b) ζ

/--
Number of subintervals sufficient for the requested analytic tolerance.

The maximum with one makes the result valid when the error constant is zero.
-/
noncomputable def requiredIntervals (a b ζ tolerance : ℝ) : ℕ :=
  PanelPlan.requiredPanels 2 12 (min a b) (max a b) ζ tolerance

/-- A planned trapezoidal mesh always contains at least one subinterval. -/
theorem requiredIntervals_pos (a b ζ tolerance : ℝ) :
    0 < requiredIntervals a b ζ tolerance :=
  PanelPlan.requiredPanels_pos ..

/-- The trapezoidal error constant is nonnegative when `ζ` is nonnegative. -/
theorem errorConstant_nonneg {a b ζ : ℝ} (hζ : 0 ≤ ζ) :
    0 ≤ errorConstant a b ζ :=
  PanelPlan.errorConstant_nonneg (by norm_num) min_le_max hζ

/--
The planned mesh controls the standard composite-trapezoidal error expression
used by mathlib.
-/
theorem trapezoidalError_le
    {a b ζ tolerance : ℝ} (htolerance : 0 < tolerance) :
    |b - a| ^ 3 * ζ /
        (12 * (requiredIntervals a b ζ tolerance : ℝ) ^ 2) ≤ tolerance := by
  have h := PanelPlan.uniformCompositeError_le (denominator := 12) (a := min a b) (b := max a b)
    (C := ζ) two_ne_zero htolerance
  rw [max_sub_min_eq_abs', abs_sub_comm, mul_comm ζ] at h
  exact h

end TrapezoidalPlan

namespace QuadratureCert

/--
Construct composite trapezoidal quadrature using the mesh selected for a
requested analytic tolerance.
-/
noncomputable def trapezoidalToTolerance
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ) :
    QuadratureCert f a b :=
  trapezoidal hf hsecond
    (TrapezoidalPlan.requiredIntervals_pos a b ζ tolerance)

/-- The certificate produced by the planner meets the requested tolerance. -/
theorem trapezoidalToTolerance_error_le
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (htolerance : 0 < tolerance) :
    (trapezoidalToTolerance (tolerance := tolerance) hf hsecond).error ≤ tolerance :=
  TrapezoidalPlan.trapezoidalError_le htolerance

/--
End-to-end analytic guarantee for tolerance-driven composite trapezoidal
quadrature.
-/
theorem trapezoidalToTolerance_sound_le
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (htolerance : 0 < tolerance) :
    ‖(∫ x in a..b, f x) -
        (trapezoidalToTolerance (tolerance := tolerance) hf hsecond).value‖ ≤ tolerance :=
  (trapezoidalToTolerance (tolerance := tolerance) hf hsecond).sound.trans
    (trapezoidalToTolerance_error_le hf hsecond htolerance)

/-! ## Joint analytic and numerical tolerance planning -/

/--
Construct a trapezoidal certificate under one total error tolerance.

The backend interval `I` encloses the exact-real trapezoidal value on the mesh
planned with analytic budget `tolerance - radius I`. Replacing that value by
the interval midpoint spends `radius I` on numerical roundoff. Thus the
certificate records the sum of the planned analytic error and the verified
roundoff error.

The construction itself does not require the remaining budget to be positive.
That condition appears only in the theorem asserting that the requested total
tolerance is met.
-/
noncomputable def trapezoidalToTotalToleranceOfInterval
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (I : ι)
    (hencloses :
      RealIntervalBackend.MemReal I
        (trapezoidalToTolerance
          (tolerance := tolerance - RealIntervalBackend.radius I)
          hf hsecond).value) :
    QuadratureCert f a b :=
  (trapezoidalToTolerance
      (tolerance := tolerance - RealIntervalBackend.radius I)
      hf hsecond).replaceValueOfInterval I hencloses

/--
If the verified numerical radius is smaller than the requested total
tolerance, automatic trapezoidal planning spends the remaining budget on
analytic truncation error and meets the total tolerance.
-/
theorem trapezoidalToTotalToleranceOfInterval_error_le
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (I : ι)
    (hencloses :
      RealIntervalBackend.MemReal I
        (trapezoidalToTolerance
          (tolerance := tolerance - RealIntervalBackend.radius I)
          hf hsecond).value)
    (hradius : RealIntervalBackend.radius I < tolerance) :
    (trapezoidalToTotalToleranceOfInterval hf hsecond I hencloses).error ≤
      tolerance :=
  le_sub_iff_add_le.mp
    (trapezoidalToTolerance_error_le hf hsecond (sub_pos.mpr hradius))

/--
End-to-end integral error bound obtained from automatic analytic planning and
a verified numerical interval under one total tolerance.
-/
theorem trapezoidalToTotalToleranceOfInterval_sound_le
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b ζ tolerance : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (I : ι)
    (hencloses :
      RealIntervalBackend.MemReal I
        (trapezoidalToTolerance
          (tolerance := tolerance - RealIntervalBackend.radius I)
          hf hsecond).value)
    (hradius : RealIntervalBackend.radius I < tolerance) :
    ‖(∫ x in a..b, f x) -
        (trapezoidalToTotalToleranceOfInterval hf hsecond I hencloses).value‖ ≤
      tolerance :=
  (trapezoidalToTotalToleranceOfInterval hf hsecond I hencloses).sound.trans
    (trapezoidalToTotalToleranceOfInterval_error_le
      hf hsecond I hencloses hradius)

end QuadratureCert

end CAS.Continuum
