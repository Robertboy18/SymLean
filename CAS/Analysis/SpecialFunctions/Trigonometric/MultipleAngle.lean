/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Multiple-angle bounds and quotients

An odd multiple of an angle keeps one factor of the cosine: `|cos ((2m+1)β)| ≤ (2m+1) |cos β|`
and `|sin ((2m+2)β)| ≤ (2m+2) |cos β|`. The quotients `sin ((n+1)β) / sin β` and
`cos ((2m+1)β) / cos β` have smooth extensions to every angle: `sineQuotient n`, the Chebyshev
polynomial `U_n (cos β)`, and `oddCosineQuotient m`, a finite cosine recurrence. For `w ≥ 0` the
derivatives of `s ↦ sin (ws)` and `s ↦ cos (ws)` of order `k` are bounded by `w ^ k`. Chebyshev
polynomials of either kind of even degree are even functions.
-/

@[expose] public noncomputable section

namespace CAS.Analysis

open _root_.Polynomial

/-- An odd multiple of an angle retains a factor of its cosine. -/
theorem abs_cos_odd_mul_le (m : ℕ) (β : ℝ) :
    |Real.cos ((2 * (m : ℝ) + 1) * β)| ≤ (2 * (m : ℝ) + 1) * |Real.cos β| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsin : |Real.sin (2 * β)| ≤ 2 * |Real.cos β| := by
      rw [Real.sin_two_mul, abs_mul, abs_mul, abs_two, mul_right_comm]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one β)
    rw [show (2 * ((m + 1 : ℕ) : ℝ) + 1) * β = (2 * (m : ℝ) + 1) * β + 2 * β by push_cast; ring,
      Real.cos_add]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ (2 * (m : ℝ) + 1) * |Real.cos β| * 1 + 1 * (2 * |Real.cos β|) := by
        rw [abs_mul, abs_mul]
        gcongr
        exacts [Real.abs_cos_le_one _, Real.abs_sin_le_one _]
      _ = _ := by push_cast; ring

/-- An even multiple of an angle has a sine with a factor of the cosine. -/
theorem abs_sin_even_mul_le (m : ℕ) (β : ℝ) :
    |Real.sin ((2 * (m : ℝ) + 2) * β)| ≤ (2 * (m : ℝ) + 2) * |Real.cos β| := by
  have hsin : |Real.sin (2 * β)| ≤ 2 * |Real.cos β| := by
    rw [Real.sin_two_mul, abs_mul, abs_mul, abs_two, mul_right_comm]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one β)
  induction m with
  | zero => simpa using hsin
  | succ m ih =>
    rw [show (2 * ((m + 1 : ℕ) : ℝ) + 2) * β = (2 * (m : ℝ) + 2) * β + 2 * β by
        push_cast; ring, Real.sin_add]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ (2 * (m : ℝ) + 2) * |Real.cos β| * 1 + 1 * (2 * |Real.cos β|) := by
        rw [abs_mul, abs_mul]
        gcongr
        exacts [Real.abs_cos_le_one _, Real.abs_cos_le_one _]
      _ = _ := by push_cast; ring

/-- The `k`th derivative of `s ↦ sin (w s)` is bounded by `w ^ k` for `w ≥ 0`. -/
theorem abs_iteratedDeriv_sin_mul_le (k : ℕ) (w t : ℝ) (hw : 0 ≤ w) :
    |iteratedDeriv k (fun s ↦ Real.sin (w * s)) t| ≤ w ^ k := by
  rw [congrFun (iteratedDeriv_comp_const_mul (Real.contDiff_sin (n := k)) w) t, abs_mul,
    abs_pow, abs_of_nonneg hw]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_iteratedDeriv_sin_le_one k _)

/-- The `k`th derivative of `s ↦ cos (w s)` is bounded by `w ^ k` for `w ≥ 0`. -/
theorem abs_iteratedDeriv_cos_mul_le (k : ℕ) (w t : ℝ) (hw : 0 ≤ w) :
    |iteratedDeriv k (fun s ↦ Real.cos (w * s)) t| ≤ w ^ k := by
  rw [congrFun (iteratedDeriv_comp_const_mul (Real.contDiff_cos (n := k)) w) t, abs_mul,
    abs_pow, abs_of_nonneg hw]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_iteratedDeriv_cos_le_one k _)

/-- The smooth extension of `sin ((n + 1) β) / sin β`, the Chebyshev polynomial `U_n (cos β)`. -/
def sineQuotient (n : ℕ) (β : ℝ) : ℝ :=
  (Chebyshev.U ℝ (n : ℤ)).eval (Real.cos β)

/-- The extension has the exact numerator at every angle, including `sin β = 0`. -/
theorem sineQuotient_mul_sin (n : ℕ) (β : ℝ) :
    sineQuotient n β * Real.sin β = Real.sin (((n : ℝ) + 1) * β) := by
  simpa only [sineQuotient, Int.cast_natCast] using
    (Chebyshev.U_real_cos (n := (n : ℤ)) (θ := β))

/-- The extended sine quotient is smooth. -/
theorem contDiff_sineQuotient (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sineQuotient n) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ (Chebyshev.U ℝ (n : ℤ)).eval t) := by
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using
      (Chebyshev.U ℝ (n : ℤ)).contDiff_aeval (𝕜 := ℝ) (⊤ : ℕ∞)
  exact hP.comp Real.contDiff_cos

/-- The finite cosine recurrence extending `cos ((2m + 1) β) / cos β`. -/
def oddCosineQuotient : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, β => 2 * Real.cos (2 * ((m + 1 : ℕ) : ℝ) * β) - oddCosineQuotient m β

/-- The recurrence has the exact numerator at every angle, including `cos β = 0`. -/
theorem cos_mul_oddCosineQuotient (m : ℕ) (β : ℝ) :
    Real.cos β * oddCosineQuotient m β = Real.cos ((2 * (m : ℝ) + 1) * β) := by
  induction m with
  | zero => simp [oddCosineQuotient]
  | succ m ih =>
    simp only [oddCosineQuotient, mul_sub, ih]
    rw [show (2 * ((m + 1 : ℕ) : ℝ) + 1) * β = 2 * ((m + 1 : ℕ) : ℝ) * β + β by ring,
      show (2 * (m : ℝ) + 1) * β = 2 * ((m + 1 : ℕ) : ℝ) * β - β by push_cast; ring,
      Real.cos_add, Real.cos_sub]
    ring

/-- The odd cosine quotient is smooth. -/
theorem contDiff_oddCosineQuotient (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (oddCosineQuotient m) := by
  induction m with
  | zero => exact contDiff_const
  | succ m ih => exact (contDiff_const.mul (contDiff_const.mul contDiff_id).cos).sub ih

/-- Chebyshev polynomials of the first kind of even degree are even functions. -/
theorem eval_neg_chebyshevT_two_mul (j : ℕ) (c : ℝ) :
    (Chebyshev.T ℝ (2 * (j : ℤ))).eval (-c) = (Chebyshev.T ℝ (2 * (j : ℤ))).eval c := by
  rw [Chebyshev.T_eval_neg, Int.negOnePow_even _ (even_two_mul _)]
  simp

/-- Chebyshev polynomials of the second kind of even degree are even functions. -/
theorem eval_neg_chebyshevU_two_mul (l : ℕ) (c : ℝ) :
    (Chebyshev.U ℝ (2 * (l : ℤ))).eval (-c) = (Chebyshev.U ℝ (2 * (l : ℤ))).eval c := by
  have hcast : (2 * (l : ℤ)) = ((2 * l : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, Chebyshev.U_eval_neg, Int.negOnePow_even _ (by rw [← hcast]; exact even_two_mul _)]
  simp

end CAS.Analysis
