/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Polynomial
import CAS.ExactTactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Exact polynomial–logarithm panel integrals

`logMonomialPrimitive n t = t^(n+1) log t / (n+1) - t^(n+1) / (n+1)²` is a primitive of
`t^n log t` away from `0` (`hasDerivAt_logMonomialPrimitive`), continuous, and zero at the
logarithmic singularity `t = 0`. Consequently the endpoint formula `integral_pow_mul_log` applies
to every panel, including panels containing the singularity and panels whose endpoints coincide
with it. No principal value is involved. For a polynomial `p`, `integral_polynomial_mul_log_sub`
gives `∫ y in a..b, p(y) log (x - y)` as the finite sum `polynomialLogPanel p a b x`, after `p`
is translated to the singularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Polynomial

namespace CAS.Analysis

/-- The continuous primitive of `t ^ n * log t`, normalized to vanish at zero.
`Real.log` already equals `log |t|` away from zero. -/
def logMonomialPrimitive (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n + 1) * Real.log t / (n + 1) - t ^ (n + 1) / (n + 1) ^ 2

/-- The singular endpoint contributes exactly zero. -/
@[simp]
theorem logMonomialPrimitive_zero (n : ℕ) : logMonomialPrimitive n 0 = 0 := by
  simp [logMonomialPrimitive]

/-- Multiplication by a positive power removes the logarithmic discontinuity at zero. -/
theorem continuous_logMonomialPrimitive (n : ℕ) : Continuous (logMonomialPrimitive n) := by
  rw [show logMonomialPrimitive n = fun t : ℝ ↦ t ^ n * (t * Real.log t) / (n + 1) -
      t ^ (n + 1) / (n + 1) ^ 2 from
    funext fun t ↦ by simp only [logMonomialPrimitive, pow_succ, mul_assoc]]
  exact (((continuous_id.pow n).mul Real.continuous_mul_log).div_const _).sub
    ((continuous_id.pow (n + 1)).div_const _)

/-- Away from zero the normalized primitive has the expected derivative. The exponent
is symbolic, so the proof uses Mathlib's natural-power derivative rule. -/
theorem hasDerivAt_logMonomialPrimitive (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logMonomialPrimitive n) (t ^ n * Real.log t) t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hp := (hasDerivAt_pow (n + 1) t)
  have hl : HasDerivAt Real.log (1 / t) t := by cas using ht
  convert ((hp.mul hl).div_const ((n : ℝ) + 1)).sub
    (hp.div_const (((n : ℝ) + 1) ^ 2)) using 1
  · rfl
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

/-- The monomial–logarithm product is absolutely integrable across zero. -/
theorem intervalIntegrable_pow_mul_log (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ n * Real.log t) volume a b :=
  intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_id.pow n).continuousOn

/-- The primitive formula from zero holds on either side of the singularity. -/
theorem integral_pow_mul_log_from_zero (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, t ^ n * Real.log t) = logMonomialPrimitive n b := by
  rcases le_total 0 b with hb | hb
  · simpa only [logMonomialPrimitive_zero, sub_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
        (continuous_logMonomialPrimitive n).continuousOn
        (fun t ht ↦ hasDerivAt_logMonomialPrimitive n ht.1.ne')
        (intervalIntegrable_pow_mul_log n 0 b)
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
      (continuous_logMonomialPrimitive n).continuousOn
      (fun t ht ↦ hasDerivAt_logMonomialPrimitive n ht.2.ne)
      (intervalIntegrable_pow_mul_log n b 0)]
    simp

/-- The same endpoint formula covers nonsingular, singular and reversed panels. -/
theorem integral_pow_mul_log (n : ℕ) (a b : ℝ) :
    (∫ t in a..b, t ^ n * Real.log t) =
      logMonomialPrimitive n b - logMonomialPrimitive n a := by
  rw [← intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_pow_mul_log n 0 b) (intervalIntegrable_pow_mul_log n 0 a),
    integral_pow_mul_log_from_zero, integral_pow_mul_log_from_zero]

/-- The finite endpoint expression for a polynomial times the logarithmic kernel.
The polynomial is translated to the singularity before its coefficients are used. -/
def polynomialLogPanel (p : ℝ[X]) (a b x : ℝ) : ℝ :=
  (p.comp (Polynomial.X + Polynomial.C x)).sum fun n c ↦
    c * (logMonomialPrimitive n (b - x) - logMonomialPrimitive n (a - x))

/-- A polynomial times the translated logarithm is interval integrable on every panel. -/
theorem intervalIntegrable_polynomial_mul_log (p : ℝ[X]) (a b x : ℝ) :
    IntervalIntegrable (fun y ↦ p.eval y * Real.log (y - x)) volume a b := by
  have hlog : IntervalIntegrable (fun y ↦ Real.log (y - x)) volume a b := by
    simpa only [sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_log' (a := a - x) (b := b - x)).comp_sub_right x
  exact hlog.continuousOn_mul p.continuous.continuousOn

/-- Integrating a polynomial against `log |t|` is a finite sum of continuous primitives. -/
theorem integral_polynomial_mul_log (p : ℝ[X]) (a b : ℝ) :
    (∫ t in a..b, p.eval t * Real.log t) =
      p.sum (fun n c ↦ c * (logMonomialPrimitive n b - logMonomialPrimitive n a)) := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun n _ ↦ by
      simp only [mul_assoc, intervalIntegral.integral_const_mul, integral_pow_mul_log]
  · intro n _
    simpa only [mul_assoc] using (intervalIntegrable_pow_mul_log n a b).const_mul (p.coeff n)

/-- Exact polynomial–logarithm integration, with no exclusion of singular panels. -/
theorem integral_polynomial_mul_log_sub (p : ℝ[X]) (a b x : ℝ) :
    (∫ y in a..b, p.eval y * Real.log (x - y)) = polynomialLogPanel p a b x := by
  have htranslate (y : ℝ) :
      p.eval y * Real.log (x - y) =
        (p.comp (Polynomial.X + Polynomial.C x)).eval (y - x) * Real.log (y - x) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, sub_add_cancel]
    rw [← Real.log_neg_eq_log (x - y), neg_sub]
  simp_rw [htranslate]
  rw [intervalIntegral.integral_comp_sub_right
    (f := fun t ↦ (p.comp (Polynomial.X + Polynomial.C x)).eval t * Real.log t),
    integral_polynomial_mul_log]
  rfl

end CAS.Analysis
