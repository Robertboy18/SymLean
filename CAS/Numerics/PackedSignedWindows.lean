/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedConvolution
public import CAS.Numerics.PackedWindows
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Windows of packed rows with a signed start

`signedWindow w x st L` is the row of the `L` slots `st, …, st + L - 1` of `x`, where slots with
a negative index are zero: a shift right by `st` slots for `st ≥ 0` and a shift left by `-st`
slots otherwise, then the low `L` slots (`signedWindow_eq`). Packing commutes with scalar
multiples and with differences of rows that do not borrow (`mul_packSlots`, `packSlots_sub`), and
the product of the reversed factors of a convolution is the reversed convolution
(`packedConvolution_reverse_factors`).

## Implementation notes

`signedWindow` is one division by a power of two, or for a negative start one multiplication,
followed by one remainder: a few big-number operations on the literal `x`, however many slots the
window holds. The signed start only selects the branch and gives the shift through `Int.toNat`,
so the arithmetic stays in natural numbers. The powers of two are `Nat.pow` rather than shifts,
so the kernel evaluates them only up to the limit stated in [PackedSlots](PackedSlots.lean).
`signedWindow_eq` identifies the window with the packed row of the shifted slots once for all
inputs, through `slot_div_two_pow` and, for the left shift, `slot_mul_two_pow`;
`packedConvolution_reverse_factors` reflects both index ranges with `Finset.sum_range_reflect`,
at the indices `p` with `p + 2 ≤ n + m`. Inside SymLean, `mul_packSlots` and `packSlots_sub`
serve the packed modules built on this one, such as [LaurentGram](LaurentGram.lean) and
[PackedSpreadSteps](PackedSpreadSteps.lean); `signedWindow` serves certificates built on the
library.
-/

@[expose] public section

namespace CAS.Numerics

/-- Slots `st, …, st + L - 1` of `x` (zero below slot `0`). -/
def signedWindow (w x : ℕ) (st : ℤ) (L : ℕ) : ℕ :=
  if 0 ≤ st then x / 2 ^ (w * st.toNat) % 2 ^ (w * L)
  else x * 2 ^ (w * (-st).toNat) % 2 ^ (w * L)

/-- Every window `signedWindow w x st L` is below `2 ^ (w * L)`. -/
theorem signedWindow_lt (w x : ℕ) (st : ℤ) (L : ℕ) : signedWindow w x st L < 2 ^ (w * L) := by
  unfold signedWindow; split_ifs <;> exact Nat.mod_lt _ (by positivity)

/-- Multiplying by `2 ^ (w * m)` moves the slots up by `m`: slot `q` of `x * 2 ^ (w * m)` is slot
`q - m` of `x` when `m ≤ q`, and `0` otherwise. -/
theorem slot_mul_two_pow (w m q x : ℕ) :
    slot w q (x * 2 ^ (w * m)) = if m ≤ q then slot w (q - m) x else 0 := by
  rw [slot_eq, slot_eq]
  split_ifs with h
  · have : w * q = w * (q - m) + w * m := by rw [← mul_add, Nat.sub_add_cancel h]
    rw [this, pow_add, Nat.mul_div_mul_right _ _ (by positivity)]
  · have h' : w * q ≤ w * m := Nat.mul_le_mul_left _ (by omega)
    have e : x * 2 ^ (w * m) / 2 ^ (w * q) = x * 2 ^ (w * (m - q)) := by
      rw [show w * m = w * (m - q) + w * q by rw [← mul_add, Nat.sub_add_cancel (by omega)],
        pow_add, ← mul_assoc, Nat.mul_div_cancel _ (by positivity)]
    rw [e]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw; simp [Nat.mod_one]
    · have : w ≤ w * (m - q) := Nat.le_mul_of_pos_right _ (by omega)
      rw [show w * (m - q) = w + (w * (m - q) - w) by omega, pow_add, mul_comm (2 ^ w),
        ← mul_assoc, Nat.mul_mod_left]

/-- For every start `st`, the window `signedWindow w x st L` is the packing of the `L` entries
`slot w (st + q).toNat x` for `0 ≤ st + q` and `0` for `st + q < 0`. -/
theorem signedWindow_eq (w x : ℕ) (st : ℤ) (L : ℕ) :
    signedWindow w x st L =
      packSlots w L fun q ↦ if 0 ≤ st + q then slot w (st + q).toNat x else 0 := by
  rw [← packSlots_slot (signedWindow_lt w x st L), packSlots_eq_sum, packSlots_eq_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [Finset.mem_range] at hq
  congr 1
  unfold signedWindow
  split_ifs with h₁ h₂ h₂
  · rw [slot_mod_two_pow hq, slot_div_two_pow]
    congr 1
    omega
  · omega
  · rw [slot_mod_two_pow hq, slot_mul_two_pow]
    simp only [show (-st).toNat ≤ q by omega, ↓reduceIte]
    congr 1
    omega
  · rw [slot_mod_two_pow hq, slot_mul_two_pow]
    simp only [show ¬ (-st).toNat ≤ q by omega, ↓reduceIte]

/-- Packing zero entries gives `0`. -/
theorem packSlots_zero (w n : ℕ) : packSlots w n (fun _ ↦ 0) = 0 := by
  simp [packSlots_eq_sum]

/-- A multiple `c * packSlots w n f` is the packing of the entries `c * f k`. -/
theorem mul_packSlots (c w n : ℕ) (f : ℕ → ℕ) :
    c * packSlots w n f = packSlots w n (fun k ↦ c * f k) := by
  simp only [packSlots_eq_sum, Finset.mul_sum, mul_assoc]

/-- If `g k ≤ f k` for every `k < n`, the natural difference of the packings of `f` and `g` is the
packing of the differences `f k - g k`. -/
theorem packSlots_sub {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ k < n, g k ≤ f k) :
    packSlots w n f - packSlots w n g = packSlots w n (fun k ↦ f k - g k) := by
  have : packSlots w n (fun k ↦ f k - g k) + packSlots w n g = packSlots w n f := by
    rw [packSlots_add]
    exact packSlots_congr fun k hk ↦ Nat.sub_add_cancel (h k hk)
  omega

/-- The coefficients of a convolution of `n` and `m` entries vanish from `n + m - 1` on. -/
theorem packedConvolution_eq_zero {n m : ℕ} (u v : ℕ → ℕ) {p : ℕ} (hp : n + m ≤ p + 1) :
    packedConvolution n m u v p = 0 := by
  unfold packedConvolution
  refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hi hj
  simp only [show ¬ (i + j = p) by omega, ↓reduceIte]

/-- The convolution of the reversed factors is the reversed convolution. -/
theorem packedConvolution_reverse_factors {n m : ℕ} (u v : ℕ → ℕ) {p : ℕ} (hp : p + 2 ≤ n + m) :
    packedConvolution n m (fun i ↦ u (n - 1 - i)) (fun j ↦ v (m - 1 - j)) p =
      packedConvolution n m u v (n + m - 2 - p) := by
  unfold packedConvolution
  set G : ℕ → ℕ → ℕ := fun a b ↦ if a + b = n + m - 2 - p then u a * v b else 0 with hG
  have h₁ : ∀ i ∈ Finset.range n, (∑ j ∈ Finset.range m,
      if i + j = p then u (n - 1 - i) * v (m - 1 - j) else 0) =
        ∑ j ∈ Finset.range m, G (n - 1 - i) (m - 1 - j) := fun i hi ↦ by
    rw [Finset.mem_range] at hi
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    simp only [hG]
    exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl h₁]
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_range_reflect (fun j ↦ G (n - 1 - i) j) m]
  exact Finset.sum_range_reflect (fun i ↦ ∑ j ∈ Finset.range m, G i j) n

end CAS.Numerics
