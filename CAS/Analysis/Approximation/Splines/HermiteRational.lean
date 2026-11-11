/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Approximation.Splines.Hermite
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import CAS.ExactTactic

/-!
# Rational Hermite coefficients centered at an evaluation point

`translatedHermiteCoefficients left h a b da db x` lists, in `ℚ`, four coefficients in powers of
`y - x`. For `h ≠ 0`, `hermitePolynomial_eval_translated` proves that they represent the cubic
`hermitePolynomial left h a b da db` exactly at every real `y`.
`differentiateCubicCoefficients` differentiates such a coefficient vector, and
`iterate_derivative_eval_translated` proves that its `k`-th iterate gives the coefficients of the
`k`-th derivative, one step at a time by `polynomial_derivative_eval_translated`.
-/

@[expose] public section

open scoped Polynomial

namespace CAS.Splines

/-- The four physical coefficients in powers of `y - x`. -/
def translatedHermiteCoefficients (left h a b da db x : ℚ) : Fin 4 → ℚ :=
  let z := (x - left) / h
  let c := -3 * a + 3 * b - h * (2 * da + db)
  let d := 2 * a - 2 * b + h * (da + db)
  ![a + h * da * z + c * z ^ 2 + d * z ^ 3,
    da + 2 * c * z / h + 3 * d * z ^ 2 / h,
    c / h ^ 2 + 3 * d * z / h ^ 2,
    d / h ^ 3]

/-- For `h ≠ 0`, the centered rational coefficients represent the physical polynomial exactly. -/
theorem hermitePolynomial_eval_translated (left h a b da db x : ℚ) (hh : h ≠ 0)
    (y : ℝ) :
    (hermitePolynomial left h a b da db).eval y =
      ∑ i : Fin 4, (translatedHermiteCoefficients left h a b da db x i : ℝ) *
        (y - (x : ℝ)) ^ i.val := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  rw [hermitePolynomial_eval]
  unfold hermiteValue translatedHermiteCoefficients
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  cas using hhR

/-- If `p` has the coefficients `c` in powers of `y - x`, then its derivative has the coefficients
`c 1`, `2 * c 2`, `3 * c 3`, `0`. -/
theorem polynomial_derivative_eval_translated {p : ℝ[X]} (c : Fin 4 → ℝ) (x : ℝ)
    (hp : ∀ y, p.eval y = ∑ i : Fin 4, c i * (y - x) ^ i.val) (y : ℝ) :
    p.derivative.eval y =
      ∑ i : Fin 4, (![c 1, 2 * c 2, 3 * c 3, 0] : Fin 4 → ℝ) i * (y - x) ^ i.val := by
  have heq : p.eval = fun z ↦ c 0 + c 1 * (z - x) +
      c 2 * (z - x) ^ 2 + c 3 * (z - x) ^ 3 := by
    funext z
    rw [hp]
    norm_num [Fin.sum_univ_succ]
    ring
  have hd : HasDerivAt (fun z ↦ c 0 + c 1 * (z - x) +
      c 2 * (z - x) ^ 2 + c 3 * (z - x) ^ 3)
      (c 1 + 2 * c 2 * (y - x) + 3 * c 3 * (y - x) ^ 2) y := by
    cas
  rw [← Polynomial.deriv, heq, hd.deriv]
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, zero_mul]
  ring

/-- Exact rational differentiation of a translated cubic coefficient vector. -/
def differentiateCubicCoefficients (c : Fin 4 → ℚ) : Fin 4 → ℚ :=
  ![c 1, 2 * c 2, 3 * c 3, 0]

/-- Repeated rational coefficient differentiation agrees with polynomial differentiation. -/
theorem iterate_derivative_eval_translated {p : ℝ[X]} (c : Fin 4 → ℚ) (x : ℝ)
    (hp : ∀ y, p.eval y = ∑ i : Fin 4, (c i : ℝ) * (y - x) ^ i.val)
    (k : ℕ) (y : ℝ) :
    (Polynomial.derivative^[k] p).eval y =
      ∑ i : Fin 4, ((differentiateCubicCoefficients^[k] c) i : ℝ) * (y - x) ^ i.val := by
  induction k generalizing y with
  | zero => exact hp y
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    convert polynomial_derivative_eval_translated
      (fun i ↦ ((differentiateCubicCoefficients^[k] c) i : ℝ)) x ih y using 1
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (· * (y - x) ^ i.val) ?_
    fin_cases i <;> simp [differentiateCubicCoefficients]

end CAS.Splines
