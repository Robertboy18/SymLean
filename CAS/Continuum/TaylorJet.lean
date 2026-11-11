/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalBackend
public import CAS.Continuum.TaylorApproximation

/-!
# Checked executable Taylor jets

`scalarTaylorPolynomialWithin` is the analytic Taylor polynomial used by
Mathlib's remainder theorem. A numerical backend, however, needs explicit
finite coefficients that it can evaluate. `TaylorJetCert` relates the two
without identifying approximate coefficients with exact derivatives.

A `TaylorJetCert` records three separate error sources:

* exact Taylor truncation, controlled by the next derivative;
* uncertainty in each stored coefficient;
* evaluation roundoff, which `TaylorJetCert.error` leaves out.

The first two are combined into an ordinary `ModelApproxCert`
(`TaylorJetCert.toModelApproxCert`). `TaylorJetCert.ofDerivativeEnclosures` takes the
coefficient and derivative enclosures from any `RealIntervalBackend`, and the resulting
approximation theorem does not depend on the backend.

## Implementation notes

We keep the stored coefficients apart from the exact ones,
`iteratedDerivWithin k f (Icc a b) a / k!`: `coefficients_sound` bounds each difference by
`coefficientErrors k`, and `approxOn_taylorJetEval_of_coefficient_bounds` turns these bounds into
the uniform error `Σ coefficientErrors k * (b - a)^k`. The truncation error is the bound of
`taylorApproxCertIcc`, and `TaylorJetCert.sound` adds the two by the triangle inequality. A backend
proposes the enclosures; `ofDerivativeEnclosures` stores the midpoint over `k!` with the radius over
`k!` as its error, and the kernel checks the membership proofs. Roundoff in evaluating the model at
a point enters afterwards, for example as the interval radius that
`ModelApproxCert.evaluateAtOfInterval` adds to the error.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace CAS.Continuum

open CAS.Certificate

/-- The exact coefficient of `(x - center)^k` in Mathlib's Taylor polynomial. -/
noncomputable def taylorCoefficientWithin
    (f : ℝ → ℝ) (s : Set ℝ) (center : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ)⁻¹ * iteratedDerivWithin k f s center

/-- Evaluate an explicitly stored order-`n` Taylor jet. -/
def taylorJetEval
    (n : ℕ) (center : ℝ) (coefficients : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), coefficients k * (x - center) ^ k

/--
Evaluate coefficients `c₀, ..., cₙ` by the ascending-coefficient Horner
recurrence.

The recursive call evaluates the tail coefficients first, so the definition
denotes

```text
(((cₙ * x + cₙ₋₁) * x + ...) * x + c₀).
```
-/
def finiteHornerEval {R : Type*} [Semiring R]
    (n : ℕ) (x : R) (coefficients : ℕ → R) : R :=
  match n with
  | 0 => coefficients 0
  | n + 1 =>
      finiteHornerEval n x (fun k ↦ coefficients (k + 1)) * x +
        coefficients 0

/-- Horner evaluation equals the corresponding finite power-basis sum. -/
theorem finiteHornerEval_eq_sum {R : Type*} [CommSemiring R]
    (n : ℕ) (x : R) (coefficients : ℕ → R) :
    finiteHornerEval n x coefficients =
      ∑ k ∈ Finset.range (n + 1), coefficients k * x ^ k := by
  induction n generalizing coefficients with
  | zero => simp [finiteHornerEval]
  | succ n ih =>
      rw [finiteHornerEval, ih, Finset.sum_range_succ' _ (n + 1), Finset.sum_mul]
      simp [pow_succ, mul_assoc]

/-- Exact Taylor coefficients recover the scalar Taylor polynomial. -/
theorem taylorJetEval_exact
    (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (center x : ℝ) :
    taylorJetEval n center
        (taylorCoefficientWithin f s center) x =
      (scalarTaylorPolynomialWithin f n s center).eval x := by
  rw [scalarTaylorPolynomialWithin_eval]
  simp [taylorJetEval, taylorCoefficientWithin, taylorWithinEval,
    taylorWithin, taylorCoeffWithin, mul_comm]

/--
Uniform contribution of coefficient uncertainty on an interval of the given
nonnegative width.
-/
def taylorCoefficientError
    (n : ℕ) (width : ℝ) (errors : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), errors k * width ^ k

/--
Per-coefficient bounds imply a uniform approximation of the exact Taylor
polynomial by the stored jet.
-/
theorem approxOn_taylorJetEval_of_coefficient_bounds
    {f : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    {coefficients errors : ℕ → ℝ}
    (hcoeff :
      ∀ k ∈ Finset.range (n + 1),
        ‖taylorCoefficientWithin f (Icc a b) a k - coefficients k‖ ≤
          errors k) :
    ApproxOn
      (fun x ↦ (scalarTaylorPolynomialWithin f n (Icc a b) a).eval x)
      (taylorJetEval n a coefficients)
      (Icc a b)
      (taylorCoefficientError n (b - a) errors) := by
  intro x hx
  change
    ‖(scalarTaylorPolynomialWithin f n (Icc a b) a).eval x -
        taylorJetEval n a coefficients x‖ ≤
      taylorCoefficientError n (b - a) errors
  rw [← taylorJetEval_exact]
  simp only [taylorJetEval, taylorCoefficientError, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  rw [← sub_mul, norm_mul, norm_pow, Real.norm_eq_abs (x - a), abs_of_nonneg hxa]
  exact mul_le_mul (hcoeff k hk) (pow_le_pow_left₀ hxa (sub_le_sub_right hx.2 a) k)
    (pow_nonneg hxa k) ((norm_nonneg _).trans (hcoeff k hk))

/--
A finite Taylor jet with checked coefficient and remainder bounds.

The coefficient function is total on `ℕ`, but only indices below `n + 1`
contribute to the model or certificate. This representation is convenient for
both exact evaluators and runtime arrays while keeping the semantic sum finite.
-/
structure TaylorJetCert
    (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) where
  /-- The panel is positively oriented or degenerate. -/
  ordered : a ≤ b
  /-- Explicit coefficients used by numerical evaluation. -/
  coefficients : ℕ → ℝ
  /-- Certified absolute uncertainty of each stored coefficient. -/
  coefficientErrors : ℕ → ℝ
  /-- Each stored coefficient encloses the corresponding exact Taylor coefficient. -/
  coefficients_sound :
    ∀ k ∈ Finset.range (n + 1),
      ‖taylorCoefficientWithin f (Icc a b) a k - coefficients k‖ ≤
        coefficientErrors k
  /-- Uniform bound for the `(n+1)`-st within derivative. -/
  derivativeBound : ℝ
  /-- Analytic regularity required by Mathlib's Taylor theorem. -/
  smooth : ContDiffOn ℝ (n + 1) f (Icc a b)
  /-- The next derivative satisfies the recorded uniform bound. -/
  derivative_sound :
    ∀ x ∈ Icc a b,
      ‖iteratedDerivWithin (n + 1) f (Icc a b) x‖ ≤ derivativeBound

/--
Construct a Taylor jet from checked derivative enclosures.

For orders `0, ..., n`, the stored coefficient is the interval midpoint
divided by `k!`, and its uncertainty is the interval radius divided by `k!`.
The final interval encloses the `(n+1)`-st derivative on the whole panel and
therefore supplies the analytic remainder constant.
-/
noncomputable def TaylorJetCert.ofDerivativeEnclosures
    {I : Type*} [RealIntervalBackend I]
    {f : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    (ordered : a ≤ b)
    (smooth : ContDiffOn ℝ (n + 1) f (Icc a b))
    (coefficientRanges : ℕ → I)
    (coefficientRanges_sound :
      ∀ k ∈ Finset.range (n + 1),
        RealIntervalBackend.MemReal (coefficientRanges k)
          (iteratedDerivWithin k f (Icc a b) a))
    (derivativeRange : I)
    (derivativeRange_sound :
      ∀ x ∈ Icc a b,
        RealIntervalBackend.MemReal derivativeRange
          (iteratedDerivWithin (n + 1) f (Icc a b) x)) :
    TaylorJetCert f n a b where
  ordered := ordered
  coefficients := fun k ↦
    (k.factorial : ℝ)⁻¹ *
      RealIntervalBackend.center (coefficientRanges k)
  coefficientErrors := fun k ↦
    (k.factorial : ℝ)⁻¹ *
      RealIntervalBackend.radius (coefficientRanges k)
  coefficients_sound := by
    intro k hk
    have hcenter :=
      RealIntervalBackend.abs_sub_center_le_radius
        (coefficientRanges_sound k hk)
    have hinv : 0 ≤ (k.factorial : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg k.factorial)
    rw [taylorCoefficientWithin, ← mul_sub, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hinv]
    exact mul_le_mul_of_nonneg_left hcenter hinv
  derivativeBound :=
    max |RealIntervalBackend.lo derivativeRange|
      |RealIntervalBackend.hi derivativeRange|
  smooth := smooth
  derivative_sound := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs
      (RealIntervalBackend.lower_mem (derivativeRange_sound x hx))
      (RealIntervalBackend.upper_mem (derivativeRange_sound x hx))

namespace TaylorJetCert

variable {f : ℝ → ℝ} {n : ℕ} {a b : ℝ}

/-- Relevant coefficient-error bounds are nonnegative because they enclose
norms. -/
theorem coefficientErrors_nonneg
    (jet : TaylorJetCert f n a b)
    (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    0 ≤ jet.coefficientErrors k :=
  (norm_nonneg
      (taylorCoefficientWithin f (Icc a b) a k - jet.coefficients k)).trans
    (jet.coefficients_sound k hk)

/-- The derivative bound is nonnegative because it bounds the next
derivative at the left endpoint of the ordered panel. -/
theorem derivativeBound_nonneg (jet : TaylorJetCert f n a b) :
    0 ≤ jet.derivativeBound :=
  (norm_nonneg
      (iteratedDerivWithin (n + 1) f (Icc a b) a)).trans
    (jet.derivative_sound a ⟨le_rfl, jet.ordered⟩)

/-- Explicit finite model represented by a Taylor jet. -/
def model (jet : TaylorJetCert f n a b) : ℝ → ℝ :=
  taylorJetEval n a jet.coefficients

/-- Error caused only by replacing exact Taylor coefficients. -/
def coefficientError (jet : TaylorJetCert f n a b) : ℝ :=
  taylorCoefficientError n (b - a) jet.coefficientErrors

/-- Coefficient uncertainty is nonnegative. -/
theorem coefficientError_nonneg (jet : TaylorJetCert f n a b) :
    0 ≤ jet.coefficientError :=
  Finset.sum_nonneg fun k hk ↦
    mul_nonneg (jet.coefficientErrors_nonneg k hk) (pow_nonneg (sub_nonneg.mpr jet.ordered) k)

/-- Analytic truncation error supplied by Mathlib's Taylor theorem. -/
noncomputable def remainderError (jet : TaylorJetCert f n a b) : ℝ :=
  jet.derivativeBound * (b - a) ^ (n + 1) / n.factorial

/-- The analytic remainder budget is nonnegative. -/
theorem remainderError_nonneg (jet : TaylorJetCert f n a b) :
    0 ≤ jet.remainderError :=
  div_nonneg
    (mul_nonneg jet.derivativeBound_nonneg
      (pow_nonneg (sub_nonneg.mpr jet.ordered) (n + 1)))
    (Nat.cast_nonneg n.factorial)

/-- Total analytic and coefficient error, excluding model-evaluation roundoff. -/
noncomputable def error (jet : TaylorJetCert f n a b) : ℝ :=
  jet.remainderError + jet.coefficientError

/-- The complete Taylor-jet error budget is nonnegative. -/
theorem error_nonneg (jet : TaylorJetCert f n a b) :
    0 ≤ jet.error :=
  add_nonneg jet.remainderError_nonneg jet.coefficientError_nonneg

/-- The exact Taylor polynomial is close to the stored finite jet. -/
theorem coefficients_approx (jet : TaylorJetCert f n a b) :
    ApproxOn
      (fun x ↦ (scalarTaylorPolynomialWithin f n (Icc a b) a).eval x)
      jet.model (Icc a b) jet.coefficientError :=
  approxOn_taylorJetEval_of_coefficient_bounds jet.coefficients_sound

/-- Mathlib's exact Taylor polynomial approximates the source function. -/
theorem remainder_approx (jet : TaylorJetCert f n a b) :
    ApproxOn f
      (fun x ↦ (scalarTaylorPolynomialWithin f n (Icc a b) a).eval x)
      (Icc a b) jet.remainderError :=
  (taylorApproxCertIcc jet.ordered jet.smooth jet.derivative_sound).sound

/-- The source function is uniformly approximated by the explicit jet. -/
theorem sound (jet : TaylorJetCert f n a b) :
    ApproxOn f jet.model (Icc a b) jet.error :=
  approxOn_trans jet.remainder_approx jet.coefficients_approx

/-- Forget Taylor-specific data and expose the ordinary approximation certificate. -/
noncomputable def toModelApproxCert (jet : TaylorJetCert f n a b) :
    ModelApproxCert ℝ ℝ (Icc a b) :=
  ModelApproxCert.ofApproxOn f jet.model n jet.error jet.sound

end TaylorJetCert

end CAS.Continuum
