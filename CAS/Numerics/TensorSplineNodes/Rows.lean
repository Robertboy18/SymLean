/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Packed row combinations with approximate inputs

A packed row combination `∑_j (s_j - α) row_j` (`packedRowCombination`) computes integer
combinations exactly once its entries fit their slots. When the coefficients approximate
`2 ^ p₁ c_j` within `e_j` and the row entries approximate `2 ^ p₂ v_j` within `f_j`, every slot is
within `∑_j (|s_j - α| f_j + e_j (|row_j| + f_j))` of `2 ^ (p₁ + p₂) ∑_j c_j v_j`
(`abs_signedSlot_packedRowCombination_sub_le`), from the product bound `abs_sum_mul_sub_le`.
`mergeRows` adds packed rows with biased slots, and `slotList` lists all slots of a packed number
(`getD_slotList`).

## Main definitions

* `mergeRows`: the sum of `L ≥ 1` packed rows with biased slots, less `L - 1` bias rows.
* `packedRowCombinationWith`: `packedRowCombination` with its bias row and the term
  `α ∑_j row_j` supplied as arguments.
* `slotList`: the slots `0, …, n - 1` of a packed number.

## Main results

* `abs_sum_mul_sub_le`: if `X_t` is within `eX_t` of `2 ^ p x_t` and `Y_t` within `eY_t` of
  `2 ^ q y_t`, then `∑ X_t Y_t` is within `∑ (|X_t| eY_t + eX_t (|Y_t| + eY_t))` of
  `2 ^ (p + q) ∑ x_t y_t`.
* `abs_signedSlot_packedRowCombination_sub_le`: every slot of a packed row combination whose
  entries fit is within the computed bound of the scaled exact combination.
* `signedSlot_mergeRows`: merged rows hold the sums of the entries, once the sums fit.
* `packedRowCombinationWith_eq`: with the bias row and the term supplied,
  `packedRowCombinationWith` is `packedRowCombination`.
* `getD_slotList`: entry `k < n` of `slotList` is slot `k`.

## Implementation notes

The tensor B-spline node certificates built on the library apply the combination twice: a first
stage contracts the coefficient tensor of one mesh level with the normal mode jets of one cell
row (rows over the tangential index), and a second stage combines tangential mode tables with the
slots of the first stage (rows over the cells of a block). The bound of
`abs_signedSlot_packedRowCombination_sub_le` is stated in the computed integers `s j - α` and
`signedSlot w k (rows j)`, so a checker can evaluate it. Its proof reads the slots exactly with
`signedSlot_packedRowCombination`, whose hypotheses it keeps (rows below `2 ^ (w * q)`, and
`FitsSlot` for the exact combination in every slot), and applies `abs_sum_mul_sub_le`, which
splits each product error as `X (Y - 2 ^ q y) + 2 ^ q y (X - 2 ^ p x)`.

Reading one slot shifts the whole row, so reading the slots of a first-stage row one by one would
shift it once per coefficient. `slotList` splits the row into halves with one mask and one shift
and recurses on both, until at most eight slots remain or `depth` halvings are spent, so the
second stage looks its coefficients up in a list. `packedRowCombinationWith` takes the bias row
and the term `α ∑_j row_j` as arguments, so that compiled code computes them once for all
combinations of the same rows (`packedRowCombinationWith_eq` holds by `rfl`), and `mergeRows`
removes the `L - 1` surplus bias rows of a sum of `L` biased rows with one multiplication and one
subtraction.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- **Products of scaled approximations.** If `X_t` is within `eX_t` of `2 ^ p x_t` and `Y_t` within
`eY_t` of `2 ^ q y_t`, then `∑ X_t Y_t` is within `∑ (|X_t| eY_t + eX_t (|Y_t| + eY_t))` of
`2 ^ (p + q) ∑ x_t y_t`. -/
theorem abs_sum_mul_sub_le {n p q : ℕ} (X Y : ℕ → ℝ) (x y eX eY : ℕ → ℝ)
    (hX : ∀ t < n, |X t - 2 ^ p * x t| ≤ eX t) (hY : ∀ t < n, |Y t - 2 ^ q * y t| ≤ eY t) :
    |∑ t ∈ range n, X t * Y t - 2 ^ (p + q) * ∑ t ∈ range n, x t * y t| ≤
      ∑ t ∈ range n, (|X t| * eY t + eX t * (|Y t| + eY t)) := by
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht ↦ ?_)
  have ht' := mem_range.mp ht
  have hy : |2 ^ q * y t| ≤ |Y t| + eY t := by
    linarith [abs_sub_abs_le_abs_sub (2 ^ q * y t) (Y t), abs_sub_comm (2 ^ q * y t) (Y t),
      hY t ht']
  rw [show X t * Y t - 2 ^ (p + q) * (x t * y t) =
      X t * (Y t - 2 ^ q * y t) + (2 ^ q * y t) * (X t - 2 ^ p * x t) by rw [pow_add]; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  linarith [mul_le_mul_of_nonneg_left (hY t ht') (abs_nonneg (X t)),
    mul_le_mul hy (hX t ht') (abs_nonneg _) ((abs_nonneg _).trans hy)]

/-- **Approximate packed row combination.** Every slot of a packed row combination whose
entries fit is within the computed bound of the scaled exact combination. -/
theorem abs_signedSlot_packedRowCombination_sub_le {w q n α : ℕ} {s rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j)))
    {k : ℕ} (hk : k < q) {p₁ p₂ : ℕ} (c v e f : ℕ → ℝ)
    (hc : ∀ j < n, |(((s j : ℤ) - α : ℤ) : ℝ) - 2 ^ p₁ * c j| ≤ e j)
    (hv : ∀ j < n, |(signedSlot w k (rows j) : ℝ) - 2 ^ p₂ * v j| ≤ f j) :
    |(signedSlot w k (packedRowCombination w q n α s rows) : ℝ) -
        2 ^ (p₁ + p₂) * ∑ j ∈ range n, c j * v j| ≤
      ∑ j ∈ range n, (|(((s j : ℤ) - α : ℤ) : ℝ)| * f j +
        e j * (|(signedSlot w k (rows j) : ℝ)| + f j)) := by
  rw [signedSlot_packedRowCombination hrows hfit hk]
  push_cast
  exact abs_sum_mul_sub_le (fun j ↦ (s j : ℝ) - α) (fun j ↦ (signedSlot w k (rows j) : ℝ))
    c v e f (fun j hj ↦ by exact_mod_cast hc j hj) hv

/-- The sum of `L ≥ 1` packed rows with biased slots, less `L - 1` bias rows. -/
def mergeRows (w q L : ℕ) (B : ℕ → ℕ) : ℕ :=
  Nat.sub (natSum L B) (Nat.mul (L - 1) (biasRow w q))

/-- Merged rows hold the sums of the entries, once the sums fit. -/
theorem signedSlot_mergeRows {w q L : ℕ} {B : ℕ → ℕ} {c : ℕ → ℕ → ℤ} (hL : 0 < L)
    (hB : ∀ m < L, (B m : ℤ) = ∑ k ∈ range q, (c m k + slotBias w) * 2 ^ (w * k))
    (hfit : ∀ k < q, FitsSlot w (∑ m ∈ range L, c m k)) {k : ℕ} (hk : k < q) :
    signedSlot w k (mergeRows w q L B) = ∑ m ∈ range L, c m k := by
  have hsum : (natSum L B : ℤ) = ∑ k ∈ range q,
      ((∑ m ∈ range L, c m k) + L * slotBias w) * 2 ^ (w * k) := by
    rw [natSum_eq_sum]
    push_cast
    rw [sum_congr rfl fun m hm ↦ hB m (mem_range.mp hm), sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_mul, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hval : (natSum L B : ℤ) - ((L - 1) * biasRow w q : ℕ) = ∑ k ∈ range q,
      ((∑ m ∈ range L, c m k) + slotBias w) * 2 ^ (w * k) := by
    rw [hsum]
    push_cast
    rw [cast_biasRow, Nat.cast_sub (by omega), mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  have hnonneg : 0 ≤ ∑ k ∈ range q, ((∑ m ∈ range L, c m k) + slotBias w) * 2 ^ (w * k) :=
    sum_nonneg fun k hk' ↦ mul_nonneg (hfit k (mem_range.mp hk')).1 (by positivity)
  have hle : (L - 1) * biasRow w q ≤ natSum L B := Int.ofNat_le.1 (by linarith)
  apply signedSlot_eq_of_cast_eq hfit _ hk
  change ((natSum L B - (L - 1) * biasRow w q : ℕ) : ℤ) = _
  rw [Nat.cast_sub hle, hval]

/-- `packedRowCombination` with its bias row `H` and the term `A = α ∑_j rows_j` supplied, so
that compiled code computes them once for all combinations of the same rows. -/
def packedRowCombinationWith (n α : ℕ) (s rows : ℕ → ℕ) (H A : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (natSum n (fun j ↦ Nat.mul (s j) (rows j))) (Nat.mul (Nat.add (Nat.mul n α) 1) H))
    (Nat.add A (Nat.mul (natSum n s) H))

/-- With the bias row `biasRow w q` and the term `α ∑ⱼ rowsⱼ` supplied, `packedRowCombinationWith`
is `packedRowCombination`. -/
theorem packedRowCombinationWith_eq (w q n α : ℕ) (s rows : ℕ → ℕ) :
    packedRowCombinationWith n α s rows (biasRow w q) (Nat.mul α (natSum n rows)) =
      packedRowCombination w q n α s rows := rfl

/-! ### Reading all slots -/

/-- The slots `0, …, n - 1` of width `w` of `x`, splitting the number in halves `depth` times
before reading slots one by one. -/
def slotList (w : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, n, x => (List.range n).map fun k ↦ slot w k x
  | depth + 1, n, x =>
    if Nat.ble n 8 then (List.range n).map fun k ↦ slot w k x
    else
      slotList w depth (n / 2) (Nat.land x (slotMask (Nat.mul w (n / 2)))) ++
        slotList w depth (n - n / 2) (Nat.shiftRight x (Nat.mul w (n / 2)))

/-- The slot list of `x` has `n` entries. -/
theorem length_slotList (w depth n x : ℕ) : (slotList w depth n x).length = n := by
  induction depth generalizing n x with
  | zero => simp [slotList]
  | succ depth ih =>
    unfold slotList
    split_ifs
    · simp
    · rw [List.length_append, ih, ih]; omega

/-- Entry `k < n` of `slotList` is slot `k`. -/
theorem getD_slotList (w depth n x : ℕ) {k : ℕ} (hk : k < n) :
    (slotList w depth n x).getD k 0 = slot w k x := by
  induction depth generalizing n x k with
  | zero => simp [slotList, List.getD_eq_getElem?_getD, hk]
  | succ depth ih =>
    unfold slotList
    split_ifs
    · simp [List.getD_eq_getElem?_getD, hk]
    · rw [List.getD_eq_getElem?_getD]
      by_cases hlo : k < n / 2
      · rw [List.getElem?_append_left (by rw [length_slotList]; exact hlo),
          ← List.getD_eq_getElem?_getD, ih _ _ hlo, Nat.mul_eq, slotMask_eq,
          show Nat.land x (2 ^ (w * (n / 2)) - 1) = x % 2 ^ (w * (n / 2)) from
            Nat.and_two_pow_sub_one_eq_mod x _, slot_mod_two_pow hlo]
      · rw [List.getElem?_append_right (by rw [length_slotList]; omega), length_slotList,
          ← List.getD_eq_getElem?_getD, ih _ _ (by omega), Nat.mul_eq,
          show Nat.shiftRight x (w * (n / 2)) = x / 2 ^ (w * (n / 2)) from
            Nat.shiftRight_eq_div_pow x _, slot_div_two_pow, Nat.sub_add_cancel (by omega)]

end CAS.Numerics
