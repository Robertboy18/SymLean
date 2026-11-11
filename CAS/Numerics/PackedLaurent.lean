/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedConvolution
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Dot products and convolution windows of packed rows

Two products of packed rows of natural numbers serve the exponential (Laurent) coefficients
of trigonometric series, which are stored symmetric about the middle slot:

* the middle slot `q - 1` of the product of two rows of `q` slots is `∑_t x_t y_{q-1-t}`
  (`slot_mul_middle_eq_sum`), the dot product `∑_t x_t y_t` when the second row is symmetric:
  one multiplication per pair of rows;
* slot `t + (q - 1)` of the product of a row `n` of `2q - 1` slots with a row `x` of `q` slots
  is the window `∑_u n_{t+q-1-u} x_u` (`slot_mul_window_eq_sum`): one multiplication applies
  a Toeplitz matrix to a row.

Both hold once every coefficient of the product stays below `2 ^ W`, which bounds on the slots
give (`packedConvolution_le_mul`, `packedConvolution_lt_of_le`).

## Implementation notes

Both are read from one product of packed rows, the Kronecker substitution of
[PackedConvolution](PackedConvolution.lean): the kernel multiplies the two literals with its
arbitrary-precision library and a shift and a mask extract the slots, so a dot product of `q`
terms or a Toeplitz matrix applied to a row costs one big multiplication. The other coefficients
of the product are computed and discarded; the slot width must hold all of them.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A coefficient of a convolution is at most `n a b` for factors bounded by `a` and `b`. -/
theorem packedConvolution_le_mul {n m a b : ℕ} {u v : ℕ → ℕ} (hu : ∀ i < n, u i ≤ a)
    (hv : ∀ j < m, v j ≤ b) (q : ℕ) : packedConvolution n m u v q ≤ n * a * b := by
  unfold packedConvolution
  calc ∑ i ∈ range n, ∑ j ∈ range m, (if i + j = q then u i * v j else 0)
      ≤ ∑ i ∈ range n, a * b := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [mem_range] at hi
        by_cases hiq : i ≤ q
        · rw [sum_ite_eq_of_mem' (range m) (q - i) _ (fun j ↦ by omega)]
          · split_ifs with h
            · exact Nat.mul_le_mul (hu i hi) (hv _ (mem_range.mp h))
            · exact Nat.zero_le _
        · rw [sum_eq_zero fun j _ ↦ by rw [ite_eq_right (by omega)]]
          exact Nat.zero_le _
    _ = n * a * b := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]
where
  /-- The sum of `if i + j = q` over `j` keeps the term `j = q - i`. -/
  sum_ite_eq_of_mem' (s : Finset ℕ) (k : ℕ) (f : ℕ → ℕ) {i q : ℕ}
      (hk : ∀ j, i + j = q ↔ j = k) :
      (∑ j ∈ s, if i + j = q then f j else 0) = if k ∈ s then f k else 0 := by
    rw [← sum_ite_eq' s k f]
    exact sum_congr rfl fun j _ ↦ by simp only [hk]

/-- Every coefficient of the product of two rows bounded by `a` and `b` is below `2 ^ W` when
`n a b < 2 ^ W`. -/
theorem packedConvolution_lt_of_le {W n m a b : ℕ} {u v : ℕ → ℕ} (hu : ∀ i < n, u i ≤ a)
    (hv : ∀ j < m, v j ≤ b) (hW : n * a * b < 2 ^ W) (q : ℕ) :
    packedConvolution n m u v q < 2 ^ W :=
  (packedConvolution_le_mul hu hv q).trans_lt hW

/-- The middle slot of the product of two rows of `q` slots is `∑_t x_t y_{q-1-t}`. -/
theorem slot_mul_middle_eq_sum {W q a b : ℕ} {x y : ℕ → ℕ} (hx : ∀ t < q, x t ≤ a)
    (hy : ∀ t < q, y t ≤ b) (hW : q * a * b < 2 ^ W) :
    slot W (q - 1) (packSlots W q x * packSlots W q y) =
      ∑ t ∈ range q, x t * y (q - 1 - t) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [packSlots, natSum, slot]
  rw [slot_packSlots_mul (fun m _ ↦ packedConvolution_lt_of_le hx hy hW m) (by omega)]
  unfold packedConvolution
  refine sum_congr rfl fun t ht ↦ ?_
  rw [mem_range] at ht
  rw [sum_eq_single (q - 1 - t)]
  · rw [ite_eq_left (by omega)]
  · exact fun j _ hj ↦ ite_eq_right (by omega)
  · exact fun h ↦ absurd (mem_range.mpr (by omega)) h

/-- Slot `t + (q - 1)` of the product of a row of `2q - 1` slots with a row of `q` slots is the
window `∑_u n_{t+q-1-u} x_u`, a Toeplitz matrix applied to `x`. -/
theorem slot_mul_window_eq_sum {W q a b : ℕ} {n x : ℕ → ℕ} (hn : ∀ s < 2 * q - 1, n s ≤ a)
    (hx : ∀ u < q, x u ≤ b) (hW : (2 * q - 1) * a * b < 2 ^ W) {t : ℕ} (ht : t < q) :
    slot W (t + (q - 1)) (packSlots W (2 * q - 1) n * packSlots W q x) =
      ∑ u ∈ range q, n (t + (q - 1) - u) * x u := by
  rw [slot_packSlots_mul (fun m _ ↦ packedConvolution_lt_of_le hn hx hW m) (by omega)]
  unfold packedConvolution
  rw [sum_comm]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [mem_range] at hu
  rw [sum_eq_single (t + (q - 1) - u)]
  · rw [ite_eq_left (by omega)]
  · exact fun j _ hj ↦ ite_eq_right (by omega)
  · exact fun h ↦ absurd (mem_range.mpr (by omega)) h

end CAS.Numerics
