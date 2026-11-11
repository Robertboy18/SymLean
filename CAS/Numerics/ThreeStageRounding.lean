/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Rounding errors of a conversion followed by an evaluation

Values `x l` known as integers `X l` within `1` of `2 ^ 48 x l` (with `|X l| ≤ 2 ^ 61`),
conversion coefficients `c l j` with `|c l j| ≤ 2 ^ 10` known within `1 / 2` of `2 ^ 80 c l j`,
the converted integers `Y j = ⌊∑ l X l C l j / 2 ^ 80⌋` and exact mode values `t j` with
`|t j| ≤ 2`: the integer evaluation `∑ j Y j (2 ^ 48 t j) / 2 ^ 96` is within
`2 q (2 ^ (-48) + n ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81))` of
`∑ j (∑ l x l c l j) t j` (`abs_conversion_evaluation_sub_le`). Without the conversion,
`∑ l X l (2 ^ 48 t l) / 2 ^ 96` is within `2 n / 2 ^ 48` of `∑ l x l t l`
(`abs_evaluation_sub_le`).

## Implementation notes

We bound each product and add the bounds. From `|X l| ≤ 2 ^ 61` we get `|x l| ≤ 2 ^ 13 + 1`, and
the split `X C / 2 ^ 128 - x c = (X / 2 ^ 48 - x) (C / 2 ^ 80) + x (C / 2 ^ 80 - c)` bounds one
product by `(2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81`. The floor in `Y j` adds `2 ^ (-48)`
after scaling, and `|t j| ≤ 2` gives the factor `2`. Only the distances of `X` and `C` from the
scaled values enter, so they may come from any rounding within those distances.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- For `l : Fin n` and `j : Fin q`, let `X l` be integers with `|X l - 2 ^ 48 * x l| ≤ 1` and
`|X l| ≤ 2 ^ 61`, `C l j` integers with `|C l j - 2 ^ 80 * c l j| ≤ 1 / 2` and `|c l j| ≤ 2 ^ 10`,
`Y j` the floor of `(∑ l, X l * C l j) / 2 ^ 80`, and `|t j| ≤ 2`. Then
`(∑ j, Y j * (2 ^ 48 * t j)) / 2 ^ 96` lies within
`q * 2 * (1 / 2 ^ 48 + n * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81))` of
`∑ j, (∑ l, x l * c l j) * t j`. -/
theorem abs_conversion_evaluation_sub_le {n q : ℕ} (x : Fin n → ℝ) (X : Fin n → ℤ)
    (c : Fin n → Fin q → ℝ) (C : Fin n → Fin q → ℤ) (Y : Fin q → ℤ) (t : Fin q → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ 48 * x l| ≤ 1) (hXb : ∀ l, |(X l : ℝ)| ≤ 2 ^ 61)
    (hC : ∀ l j, |(C l j : ℝ) - 2 ^ 80 * c l j| ≤ 1 / 2) (hc : ∀ l j, |c l j| ≤ 2 ^ 10)
    (hY : ∀ j, (Y j : ℝ) ≤ (∑ l, (X l : ℝ) * C l j) / 2 ^ 80 ∧
      (∑ l, (X l : ℝ) * C l j) / 2 ^ 80 < Y j + 1)
    (ht : ∀ j, |t j| ≤ 2) :
    |(∑ j, (Y j : ℝ) * (2 ^ 48 * t j)) / 2 ^ 96 - ∑ j, (∑ l, x l * c l j) * t j| ≤
      (q : ℝ) * 2 * (1 / 2 ^ 48 + (n : ℝ) * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81)) := by
  have hterm : ∀ l j, |(X l : ℝ) * C l j / 2 ^ 128 - x l * c l j| ≤
      (2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81 := by
    intro l j
    obtain ⟨hX₁, hX₂⟩ := abs_le.mp (hX l)
    obtain ⟨hXb₁, hXb₂⟩ := abs_le.mp (hXb l)
    obtain ⟨hC₁, hC₂⟩ := abs_le.mp (hC l j)
    obtain ⟨hc₁, hc₂⟩ := abs_le.mp (hc l j)
    have ha : |(X l : ℝ) / 2 ^ 48 - x l| ≤ 1 / 2 ^ 48 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hb : |(C l j : ℝ) / 2 ^ 80| ≤ 2 ^ 10 + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hx : |x l| ≤ 2 ^ 13 + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hd : |(C l j : ℝ) / 2 ^ 80 - c l j| ≤ 1 / 2 ^ 81 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [show (X l : ℝ) * C l j / 2 ^ 128 - x l * c l j =
        ((X l : ℝ) / 2 ^ 48 - x l) * (C l j / 2 ^ 80) + x l * (C l j / 2 ^ 80 - c l j) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    linarith [mul_le_mul ha hb (abs_nonneg _) (by positivity),
      mul_le_mul hx hd (abs_nonneg _) (by positivity)]
  have hE : ∀ j, |(Y j : ℝ) / 2 ^ 48 - ∑ l, x l * c l j| ≤
      1 / 2 ^ 48 + (n : ℝ) * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81) := by
    intro j
    have hS : |(∑ l, (X l : ℝ) * C l j) / 2 ^ 128 - ∑ l, x l * c l j| ≤
        (n : ℝ) * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81) := by
      rw [sum_div, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun l _ ↦ hterm l j).trans ?_)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨hS₁, hS₂⟩ := abs_le.mp hS
    obtain ⟨hY₁, hY₂⟩ := hY j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsplit : (∑ j, (Y j : ℝ) * (2 ^ 48 * t j)) / 2 ^ 96 - ∑ j, (∑ l, x l * c l j) * t j =
      ∑ j, ((Y j : ℝ) / 2 ^ 48 - ∑ l, x l * c l j) * t j := by
    rw [sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |((Y j : ℝ) / 2 ^ 48 - ∑ l, x l * c l j) * t j| ≤
        ∑ _j : Fin q,
          (1 / 2 ^ 48 + (n : ℝ) * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81)) * 2 :=
        sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (hE j) (ht j) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For integers `X l` with `|X l - 2 ^ 48 * x l| ≤ 1` and reals `t l` with `|t l| ≤ 2`, the value
`(∑ l, X l * (2 ^ 48 * t l)) / 2 ^ 96` lies within `n * 2 / 2 ^ 48` of `∑ l, x l * t l`. -/
theorem abs_evaluation_sub_le {n : ℕ} (x : Fin n → ℝ) (X : Fin n → ℤ) (t : Fin n → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ 48 * x l| ≤ 1) (ht : ∀ l, |t l| ≤ 2) :
    |(∑ l, (X l : ℝ) * (2 ^ 48 * t l)) / 2 ^ 96 - ∑ l, x l * t l| ≤ (n : ℝ) * 2 / 2 ^ 48 := by
  have hsplit : (∑ l, (X l : ℝ) * (2 ^ 48 * t l)) / 2 ^ 96 - ∑ l, x l * t l =
      ∑ l, ((X l : ℝ) - 2 ^ 48 * x l) / 2 ^ 48 * t l := by
    rw [sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun l _ ↦ by ring
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |((X l : ℝ) - 2 ^ 48 * x l) / 2 ^ 48 * t l| ≤ ∑ _l : Fin n, 1 / 2 ^ 48 * 2 :=
        sum_le_sum fun l _ ↦ by
          rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48)]
          exact mul_le_mul (div_le_div_of_nonneg_right (hX l) (by positivity)) (ht l)
            (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end CAS.Numerics
