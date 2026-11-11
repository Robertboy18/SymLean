/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Integer evaluation of separable double sums

A separable sum `∑ m, ∑ l, c m l * r m * a l` is evaluated in integers from approximations `C`,
`R` and `A` of `2 ^ pc c`, `2 ^ pr r` and `2 ^ pa a`, each within `1`, first as the inner sums
`∑ m, R m * C m l` and then as their combination with `A`. When `|r m| ≤ 1` and `|a l| ≤ 1`,
the integer result divided by `2 ^ (pc + pr + pa)` is within
`M L (1 + 2 ^ (-pr)) (1 + 2 ^ (-pa)) / 2 ^ pc + B ((1 + 2 ^ (-pa)) / 2 ^ pr + 1 / 2 ^ pa)` of the
sum, where `B` bounds `∑ m, ∑ l, |c m l|` (`abs_separable_sub_le`). Packed evaluations of
trigonometric expansions on grids are of this form; `natAbs_le_of_abs_sub_le` bounds the
approximations themselves, for the slot widths of the packed sums.

## Implementation notes

We sum over `m` first. The inner sums `∑ m, R m * C m l` do not involve `A`, so on a grid of
points they are formed once for each `R` and reused for every `A`; this is the usual
factorization of a separable sum. The integer evaluation is exact, so all of the error comes from
the approximations, and we bound it term by term: one product of three scaled approximations is
within `(1 + 2 ^ (-pr)) (1 + 2 ^ (-pa)) / 2 ^ pc + |c m l| ((1 + 2 ^ (-pa)) / 2 ^ pr + 1 / 2 ^ pa)`
of `c m l * r m * a l` (`abs_scaled_triple_sub_le`), and the `M L` terms add up to the bound.
Only `|C - 2 ^ pc c| ≤ 1` and its analogues are used, so untrusted code may round the
approximations in either direction.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The error of a product of three scaled approximations. -/
private theorem abs_scaled_triple_sub_le {c r a C R A sc sr sa : ℝ}
    (hsc : 0 < sc) (hsr : 0 < sr) (hsa : 0 < sa) (hr : |r| ≤ 1) (ha : |a| ≤ 1)
    (hC : |C - sc * c| ≤ 1) (hR : |R - sr * r| ≤ 1) (hA : |A - sa * a| ≤ 1) :
    |C / sc * (R / sr) * (A / sa) - c * r * a| ≤
      (1 + 1 / sr) * (1 + 1 / sa) / sc + |c| * ((1 + 1 / sa) / sr + 1 / sa) := by
  have key : ∀ {X x s : ℝ}, 0 < s → |X - s * x| ≤ 1 → |X / s - x| ≤ 1 / s := fun {X x s} hs h ↦ by
    rw [show X / s - x = (X - s * x) / s by field_simp, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right h hs.le
  have hc' := key hsc hC
  have hr' := key hsr hR
  have ha' := key hsa hA
  have hR1 : |R / sr| ≤ 1 + 1 / sr := by linarith [abs_sub_abs_le_abs_sub (R / sr) r]
  have hA1 : |A / sa| ≤ 1 + 1 / sa := by linarith [abs_sub_abs_le_abs_sub (A / sa) a]
  have hid : C / sc * (R / sr) * (A / sa) - c * r * a =
      (C / sc - c) * (R / sr) * (A / sa) + c * (R / sr - r) * (A / sa) +
        c * r * (A / sa - a) := by ring
  rw [hid]
  have h1 : |(C / sc - c) * (R / sr) * (A / sa)| ≤ 1 / sc * (1 + 1 / sr) * (1 + 1 / sa) := by
    rw [abs_mul, abs_mul]
    gcongr
  have h2 : |c * (R / sr - r) * (A / sa)| ≤ |c| * (1 / sr) * (1 + 1 / sa) := by
    rw [abs_mul, abs_mul]
    gcongr
  have h3 : |c * r * (A / sa - a)| ≤ |c| * 1 * (1 / sa) := by
    rw [abs_mul, abs_mul]
    gcongr
  calc _ ≤ |(C / sc - c) * (R / sr) * (A / sa)| + |c * (R / sr - r) * (A / sa)| +
        |c * r * (A / sa - a)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ 1 / sc * (1 + 1 / sr) * (1 + 1 / sa) + |c| * (1 / sr) * (1 + 1 / sa) +
        |c| * 1 * (1 / sa) := by linarith
    _ = _ := by field_simp; ring

/-- **Integer evaluation of a separable sum.** The two-stage integer sum with approximations
within `1` of `2 ^ pc c`, `2 ^ pr r` and `2 ^ pa a` approximates `∑ m, ∑ l, c m l * r m * a l`
after division by `2 ^ (pc + pr + pa)`. -/
theorem abs_separable_sub_le {M L : ℕ} (c : Fin M → Fin L → ℝ) (r : Fin M → ℝ)
    (a : Fin L → ℝ) (C : Fin M → Fin L → ℤ) (R : Fin M → ℤ) (A : Fin L → ℤ) (pc pr pa : ℕ)
    {B : ℝ} (hB : ∑ m, ∑ l, |c m l| ≤ B) (hr : ∀ m, |r m| ≤ 1) (ha : ∀ l, |a l| ≤ 1)
    (hC : ∀ m l, |(C m l : ℝ) - 2 ^ pc * c m l| ≤ 1)
    (hR : ∀ m, |(R m : ℝ) - 2 ^ pr * r m| ≤ 1)
    (hA : ∀ l, |(A l : ℝ) - 2 ^ pa * a l| ≤ 1) :
    |((∑ l, (∑ m, R m * C m l) * A l : ℤ) : ℝ) / 2 ^ (pc + pr + pa) -
        ∑ m, ∑ l, c m l * r m * a l| ≤
      M * L * ((1 + 1 / 2 ^ pr) * (1 + 1 / 2 ^ pa) / 2 ^ pc) +
        B * ((1 + 1 / 2 ^ pa) / 2 ^ pr + 1 / 2 ^ pa) := by
  have hsc : (0 : ℝ) < 2 ^ pc := by positivity
  have hsr : (0 : ℝ) < 2 ^ pr := by positivity
  have hsa : (0 : ℝ) < 2 ^ pa := by positivity
  have hval : ((∑ l, (∑ m, R m * C m l) * A l : ℤ) : ℝ) / 2 ^ (pc + pr + pa) =
      ∑ m, ∑ l, (C m l : ℝ) / 2 ^ pc * ((R m : ℝ) / 2 ^ pr) * ((A l : ℝ) / 2 ^ pa) := by
    push_cast
    simp only [Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun m _ ↦ sum_congr rfl fun l _ ↦ ?_
    rw [pow_add, pow_add]
    field_simp
  rw [hval, ← sum_sub_distrib]
  set E : ℝ := (1 + 1 / 2 ^ pr) * (1 + 1 / 2 ^ pa) / 2 ^ pc
  set F : ℝ := (1 + 1 / 2 ^ pa) / 2 ^ pr + 1 / 2 ^ pa
  have hF : 0 ≤ F := by positivity
  calc _ ≤ ∑ m, |∑ l, ((C m l : ℝ) / 2 ^ pc * ((R m : ℝ) / 2 ^ pr) * ((A l : ℝ) / 2 ^ pa)) -
        ∑ l, c m l * r m * a l| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, ∑ l, (E + |c m l| * F) := by
      refine sum_le_sum fun m _ ↦ ?_
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_)
      exact abs_scaled_triple_sub_le hsc hsr hsa (hr m) (ha l) (hC m l) (hR m) (hA l)
    _ = M * L * E + (∑ m, ∑ l, |c m l|) * F := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← sum_mul]
      ring
    _ ≤ M * L * E + B * F := by gcongr

/-- An integer within `1` of `2 ^ p y` with `|y| ≤ 1` has absolute value at most `2 ^ p + 1`. -/
theorem natAbs_le_of_abs_sub_le {x : ℤ} {y : ℝ} {p : ℕ} (hx : |(x : ℝ) - 2 ^ p * y| ≤ 1)
    (hy : |y| ≤ 1) : x.natAbs ≤ 2 ^ p + 1 := by
  have h1 : |(2 : ℝ) ^ p * y| ≤ 2 ^ p := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p)]
    exact mul_le_of_le_one_right (by positivity) hy
  have h2 : |(x : ℝ)| ≤ 2 ^ p + 1 := by linarith [abs_sub_abs_le_abs_sub (x : ℝ) (2 ^ p * y)]
  have h3 : |x| ≤ 2 ^ p + 1 := by exact_mod_cast h2
  rw [Int.abs_eq_natAbs] at h3
  exact_mod_cast h3

end CAS.Numerics
