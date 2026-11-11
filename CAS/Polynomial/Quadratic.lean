/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Complete real quadratic solution predicates

Mathlib's quadratic formula, specialized to the nonnegative real square root. For `a ≠ 0` and a
nonnegative discriminant, `quadratic_eq_zero_iff_sqrt` and `quadratic_eq_zero_iff_centre` describe
every real solution of `a * (x * x) + b * x + c = 0`, rather than only verifying proposed roots;
for a negative discriminant `quadratic_eq_zero_iff_false` excludes every real solution, and
`sqrt_div_eq_sqrt_mul_div` clears the denominator under a square root. `#cas [solve x]` and
`#cas [reduce x]` treat the linear and constant cases (`a = 0`) separately before they use these
theorems.
-/

public section

namespace CAS.Polynomial

/-- A nondegenerate real quadratic with nonnegative discriminant has these exact roots. -/
theorem quadratic_eq_zero_iff_sqrt (a b c x : ℝ) (ha : a ≠ 0)
    (hd : 0 ≤ discrim a b c) :
    a * (x * x) + b * x + c = 0 ↔
      x = (-b + Real.sqrt (discrim a b c)) / (2 * a) ∨
        x = (-b - Real.sqrt (discrim a b c)) / (2 * a) :=
  quadratic_eq_zero_iff ha (by rw [← sq, Real.sq_sqrt hd]) x

/-- The roots of a nondegenerate real quadratic with nonnegative discriminant, around the
centre `-b / (2 a)`. -/
theorem quadratic_eq_zero_iff_centre (a b c x : ℝ) (ha : a ≠ 0) (hd : 0 ≤ discrim a b c) :
    a * (x * x) + b * x + c = 0 ↔
      x = -b / (2 * a) + Real.sqrt (discrim a b c / (4 * a ^ 2)) ∨
        x = -b / (2 * a) - Real.sqrt (discrim a b c / (4 * a ^ 2)) := by
  set s := Real.sqrt (discrim a b c / (4 * a ^ 2))
  have hD : 0 ≤ discrim a b c / (4 * a ^ 2) := div_nonneg hd (by positivity)
  have hs : discrim a b c = (2 * a * s) * (2 * a * s) := by
    calc discrim a b c = 4 * a ^ 2 * (discrim a b c / (4 * a ^ 2)) := by field_simp
      _ = _ := by rw [← Real.mul_self_sqrt hD]; ring
  have e1 : (-b + 2 * a * s) / (2 * a) = -b / (2 * a) + s := by field_simp
  have e2 : (-b - 2 * a * s) / (2 * a) = -b / (2 * a) - s := by field_simp
  rw [quadratic_eq_zero_iff ha hs x, e1, e2]

/-- A square root of a quotient with a rational denominator: `√(n / m) = √(n j) / k` when
`m j = k ^ 2`, for example `j = 1` when `m` is a square and `j = k = m` otherwise. -/
theorem sqrt_div_eq_sqrt_mul_div {n m j k : ℝ} (hj : 0 < j) (hk : 0 < k) (h : m * j = k ^ 2) :
    Real.sqrt (n / m) = Real.sqrt (n * j) / k := by
  have hq : n / m = n * j / k ^ 2 := by rw [← h, mul_div_mul_right _ _ hj.ne']
  rw [hq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hk.le]

/-- A negative discriminant excludes every real root. -/
theorem quadratic_eq_zero_iff_false (a b c x : ℝ) (hd : discrim a b c < 0) :
    a * (x * x) + b * x + c = 0 ↔ False :=
  iff_false_intro fun h ↦ hd.not_ge (discrim_eq_sq_of_quadratic_eq_zero h ▸ sq_nonneg _)

end CAS.Polynomial
