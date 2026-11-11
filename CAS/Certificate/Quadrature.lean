/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CAS.Certificate.Approximation

/-!
# Verified quadrature certificates

A `QuadratureCert f a b` stores a proposed value for Mathlib's interval integral of `f`
from `a` to `b`, an error budget, and a proof of the bound
`‖(∫ x in a..b, f x) - value‖ ≤ error`. It does not depend on a numerical backend.

## Main definitions

* `QuadratureCert`, with `QuadratureCert.ofErrorBound` and `QuadratureCert.weaken`.
* `QuadratureCert.addAdjacent`: the certificate on `[a, b]` from certificates on `[a, m]` and
  `[m, b]`; the values and the budgets add.
* `QuadratureCert.transportApprox`: a certificate for `f` from one for `g` and a uniform bound
  `ε` on `f - g` over `[[a, b]]`, at the extra cost `ε |b - a|`.
* `QuadratureCert.replaceValue`: the value replaced by a computed one, at the extra cost of a
  bound on their distance.

## Main results

* `QuadratureCert.error_nonneg`: every error budget is nonnegative.
* `QuadratureCert.integral_mem_Icc`: for a real integrand, the integral lies in
  `[value - error, value + error]`.
* `QuadratureCert.norm_intervalIntegral_sub_le`: a uniform bound `ε` on `[[a, b]]` bounds the
  difference of the two integrals by `ε |b - a|`.

## Implementation notes

Mathlib's interval integral is total: it is `0` for a function that is not interval
integrable. A certificate therefore bounds the distance to that total value and says nothing
about `IntervalIntegrable f volume a b`; `QuadratureRule.ExactFor` follows the same convention.
The constructors that split an integral (`addAdjacent`) or transport a uniform integrand
error (`transportApprox`) take the integrability hypotheses they need as arguments.

We keep three sources of error apart, and each enters the budget by the triangle inequality:

* an analytic quadrature theorem controls the difference between the exact
  integral and an exact-real quadrature formula;
* `transportApprox` replaces the integrand by a simpler model under an approximation
  certificate;
* `replaceValue` replaces the exact-real formula value by a computed value under a roundoff
  bound.

The structure lives in the `CAS.Continuum` namespace because it is
about an interval integral, but the module sits with the other certificates so
that tactics can inspect it without importing interval evaluators, quadrature
planners, or the CEGA query machinery.
-/

@[expose] public section

open MeasureTheory
open CAS.Certificate

namespace CAS.Continuum

/--
A checked approximation to Mathlib's totalized interval integral of `f`
from `a` to `b`.

The value is an element of `E`. A decoded floating-point result may be used as the value
once its distance to an exact value is bounded, as in `replaceValue`.
-/
structure QuadratureCert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) where
  /-- Proposed value of the interval integral. -/
  value : E
  /-- Certified upper bound for the norm error. -/
  error : ℝ
  /-- The error bound for Mathlib's total interval integral. -/
  sound : ‖(∫ x in a..b, f x) - value‖ ≤ error

namespace QuadratureCert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {a b : ℝ}

/-! ## Basic constructors and projections -/

/-- The certificate of an already proved error estimate for the interval integral. -/
def ofErrorBound (value : E) (error : ℝ)
    (h : ‖(∫ x in a..b, f x) - value‖ ≤ error) :
    QuadratureCert f a b where
  value := value
  error := error
  sound := h

/--
Combine certificates on two adjacent oriented intervals.

No ordering assumption on `a`, `m`, and `b` is required: interval integrals
are oriented, and their additivity only needs integrability on the two pieces.
The proposed values and error budgets add.
-/
def addAdjacent
    {f : ℝ → E} {a m b : ℝ}
    (left : QuadratureCert f a m)
    (right : QuadratureCert f m b)
    (hleft : IntervalIntegrable f volume a m)
    (hright : IntervalIntegrable f volume m b) :
    QuadratureCert f a b where
  value := left.value + right.value
  error := left.error + right.error
  sound := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hsplit :
        ((∫ x in a..m, f x) + ∫ x in m..b, f x) -
            (left.value + right.value) =
          ((∫ x in a..m, f x) - left.value) +
            ((∫ x in m..b, f x) - right.value) := by
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add left.sound right.sound)

/-- The proposed value of a combined certificate is the sum of the two proposed values. -/
@[simp]
theorem addAdjacent_value
    {f : ℝ → E} {a m b : ℝ}
    (left : QuadratureCert f a m)
    (right : QuadratureCert f m b)
    (hleft : IntervalIntegrable f volume a m)
    (hright : IntervalIntegrable f volume m b) :
    (left.addAdjacent right hleft hright).value =
      left.value + right.value :=
  rfl

/-- The error budget of a combined certificate is the sum of the two error budgets. -/
@[simp]
theorem addAdjacent_error
    {f : ℝ → E} {a m b : ℝ}
    (left : QuadratureCert f a m)
    (right : QuadratureCert f m b)
    (hleft : IntervalIntegrable f volume a m)
    (hright : IntervalIntegrable f volume m b) :
    (left.addAdjacent right hleft hright).error =
      left.error + right.error :=
  rfl

/-- Every quadrature certificate has a nonnegative error budget. -/
theorem error_nonneg (q : QuadratureCert f a b) : 0 ≤ q.error :=
  (norm_nonneg _).trans q.sound

/-- Weaken a quadrature certificate to a larger error budget. -/
def weaken (q : QuadratureCert f a b) {error' : ℝ}
    (herror : q.error ≤ error') : QuadratureCert f a b where
  value := q.value
  error := error'
  sound := q.sound.trans herror

/--
For scalar integrands, enclose the totalized interval integral in a conventional
closed interval around the proposed value.
-/
theorem integral_mem_Icc {f : ℝ → ℝ} {a b : ℝ}
    (q : QuadratureCert f a b) :
    (∫ x in a..b, f x) ∈ Set.Icc (q.value - q.error) (q.value + q.error) := by
  have hsound := q.sound
  rw [Real.norm_eq_abs] at hsound
  rcases abs_le.mp hsound with ⟨hlower, hupper⟩
  constructor <;> linarith

end QuadratureCert

end CAS.Continuum

namespace CAS.Continuum

namespace QuadratureCert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ}

/-! ## Integration of uniform approximation certificates -/

/--
Uniform approximation on the unoriented interval controls the difference of
the corresponding interval integrals.

The `IntervalIntegrable` hypotheses are needed only to rewrite the integral of
the pointwise difference as the difference of the integrals.  The estimate
itself is the standard Bochner-integral norm bound.
-/
theorem norm_intervalIntegral_sub_le
    (c : ApproxCert ℝ E (Set.uIcc a b))
    (hlhs : IntervalIntegrable c.lhs volume a b)
    (hrhs : IntervalIntegrable c.rhs volume a b) :
    ‖(∫ x in a..b, c.lhs x) - ∫ x in a..b, c.rhs x‖ ≤
      c.eps * |b - a| := by
  rw [← intervalIntegral.integral_sub hlhs hrhs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦
    c.sound x (Set.uIoc_subset_uIcc hx)

variable {f g : ℝ → E}

/--
Transport a quadrature certificate across a uniformly certified integrand
approximation.

If `lhs` is uniformly within `ε` of `rhs` on `[[a,b]]`, and `rhs` has a
quadrature certificate with error `δ`, then the same proposed value
approximates the integral of `lhs` with error `ε |b-a| + δ`.
-/
noncomputable def transportApprox
    (c : ApproxCert ℝ E (Set.uIcc a b))
    (q : QuadratureCert c.rhs a b)
    (hlhs : IntervalIntegrable c.lhs volume a b)
    (hrhs : IntervalIntegrable c.rhs volume a b) :
    QuadratureCert c.lhs a b where
  value := q.value
  error := c.eps * |b - a| + q.error
  sound := by
    have hsplit :
        (∫ x in a..b, c.lhs x) - q.value =
          ((∫ x in a..b, c.lhs x) - ∫ x in a..b, c.rhs x) +
            ((∫ x in a..b, c.rhs x) - q.value) := by
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_intervalIntegral_sub_le c hlhs hrhs) q.sound)

/-! ## Verified numerical-value replacement -/

/--
Replace the exact-real quadrature value by a computed value.

The hypothesis is the only obligation placed on a floating-point or other
numerical backend.  A directed-rounding interval, an IEEE error analysis, or
an exact rational computation can all prove this same norm inequality.  The
analytic and numerical errors then add by the triangle inequality.
-/
def replaceValue (q : QuadratureCert f a b) (computed : E) (roundoff : ℝ)
    (hroundoff : ‖q.value - computed‖ ≤ roundoff) :
    QuadratureCert f a b where
  value := computed
  error := q.error + roundoff
  sound := by
    have hsplit :
        (∫ x in a..b, f x) - computed =
          ((∫ x in a..b, f x) - q.value) + (q.value - computed) := by
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add q.sound hroundoff)

/-- Replacing a certified value adds the backend roundoff to the analytic error. -/
theorem replaceValue_sound
    (q : QuadratureCert f a b) (computed : E) (roundoff : ℝ)
    (hroundoff : ‖q.value - computed‖ ≤ roundoff) :
    ‖(∫ x in a..b, f x) - computed‖ ≤ q.error + roundoff :=
  (q.replaceValue computed roundoff hroundoff).sound

/-- After replacing the value, the certificate stores the computed value. -/
@[simp]
theorem replaceValue_value
    (q : QuadratureCert f a b) (computed : E) (roundoff : ℝ)
    (hroundoff : ‖q.value - computed‖ ≤ roundoff) :
    (q.replaceValue computed roundoff hroundoff).value = computed :=
  rfl

/-- After replacing the value, the error budget is the analytic error plus the roundoff. -/
@[simp]
theorem replaceValue_error
    (q : QuadratureCert f a b) (computed : E) (roundoff : ℝ)
    (hroundoff : ‖q.value - computed‖ ≤ roundoff) :
    (q.replaceValue computed roundoff hroundoff).error =
      q.error + roundoff :=
  rfl

end QuadratureCert

end CAS.Continuum
