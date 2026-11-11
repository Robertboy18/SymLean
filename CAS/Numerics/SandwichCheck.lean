/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.MatrixPositivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# An exact check of the sandwich certificate `g B - B A B ⪰ 0`

For dyadic matrices `B = B' / 2 ^ β` and `A = A' / 2 ^ α` with integer numerators and a dyadic
`g = g' / 2 ^ γ`, the matrix `2 ^ (γ + 2β + α) (g B - B A B)` has the integer entries
`sandwichNumerator` `g' B' 2 ^ (β + α) - 2 ^ γ (B' A' B')`. `sandwichCheck` confirms the stored
product `B' A'` (so that every entry of `B' A' B'` costs one row of products) and passes the
integer matrix to the dense `LDLᵀ` check `ldltCheck` of
[MatrixPositivity](MatrixPositivity.lean) with a shift `τ ≥ 0`;
`quadForm_sandwich_nonneg_of_sandwichCheck` then gives the quadratic-form certificate used by
the sandwich bounds of the finite-rank determinant criterion. The check costs about `7 n³`
integer products.

## Implementation notes

Untrusted code proposes the product `B' A'`, the factor `L`, the weights `d` and `τ`; the kernel
checks the product entry by entry, `0 ≤ τ`, and `ldltCheck` on the numerators, all in exact
integers since every scale is a power of two. Checking a stored product keeps the cost cubic:
an entry of `B' A' B'` computed from the factors alone would cost `n²` products.
`quadForm_sandwich_nonneg_of_sandwichCheck` takes the bound of `quadForm_ge_of_ldltCheck` for the
numerators over `2 ^ (γ + 2 β + α)` and identifies them with the entries of `g B - B A B`.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

variable {n : ℕ}

/-- The integer numerators of `2 ^ (γ + 2β + α) (g B - B A B)`, with the stored product
`BA' = B' A'`. -/
def sandwichNumerator (B' BA' : Fin n → Fin n → ℤ) (g' : ℤ) (α β γ : ℕ) (i j : Fin n) : ℤ :=
  g' * B' i j * 2 ^ (β + α) - 2 ^ γ * ∑ l, BA' i l * B' l j

/-- The check of the sandwich certificate: the stored product and the dense `LDLᵀ` check of
the numerators. -/
def sandwichCheck (A' B' BA' L : Fin n → Fin n → ℤ) (d : Fin n → ℕ) (g' : ℤ) (α β γ : ℕ)
    (τ : ℚ) : Bool :=
  decide (∀ i j, BA' i j = ∑ k, B' i k * A' k j) && decide (0 ≤ τ) &&
    ldltCheck (sandwichNumerator B' BA' g' α β γ) L d (γ + 2 * β + α) τ

/-- **Sandwich certificate.** A passing `sandwichCheck` gives
`0 ≤ vᵀ (g B - B A B) v` for `B = B' / 2 ^ β`, `A = A' / 2 ^ α` and `g = g' / 2 ^ γ`. -/
theorem quadForm_sandwich_nonneg_of_sandwichCheck {A' B' BA' L : Fin n → Fin n → ℤ}
    {d : Fin n → ℕ} {g' : ℤ} {α β γ : ℕ} {τ : ℚ}
    (h : sandwichCheck A' B' BA' L d g' α β γ τ = true) (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, (((g' : ℝ) / 2 ^ γ) * (Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β) i j -
      ((Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β) * (Matrix.of fun i j ↦ (A' i j : ℝ) / 2 ^ α) *
        (Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β)) i j) * v i * v j := by
  simp only [sandwichCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hBA, hτ⟩, hl⟩ := h
  have hq := quadForm_ge_of_ldltCheck _ L d _ τ hl v
  have hentry : ∀ i j, (sandwichNumerator B' BA' g' α β γ i j : ℝ) / 2 ^ (γ + 2 * β + α) =
      ((g' : ℝ) / 2 ^ γ) * (Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β) i j -
      ((Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β) * (Matrix.of fun i j ↦ (A' i j : ℝ) / 2 ^ α) *
        (Matrix.of fun i j ↦ (B' i j : ℝ) / 2 ^ β)) i j := fun i j ↦ by
    have hpow : (2 : ℝ) ^ (γ + 2 * β + α) = 2 ^ γ * 2 ^ β * 2 ^ β * 2 ^ α := by ring
    simp only [sandwichNumerator, Matrix.mul_apply, Matrix.of_apply, hBA]
    push_cast
    rw [sub_div, hpow]
    congr 1
    · rw [pow_add]
      field_simp
    · simp only [mul_sum, sum_mul, sum_div]
      refine sum_congr rfl fun l _ ↦ sum_congr rfl fun k _ ↦ ?_
      field_simp
  exact (mul_nonneg (by exact_mod_cast hτ) (by positivity)).trans
    (hq.trans_eq (sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hentry]))

end CAS.Numerics
