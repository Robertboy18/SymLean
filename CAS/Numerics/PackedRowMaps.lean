/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLaurent
public import CAS.Numerics.PackedRounding
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Slotwise maps, small biases and dot products of packed rows

`mapRowByHalving f w o d x` of [PackedRounding](PackedRounding.lean) applies `f` to the `2 ^ d`
slots of width `w` of `x` and repacks the results in slots of width `o`
(`slot_mapRowByHalving`). With `f = rebiasSlot w β` it moves the biased slots of a row to the
smaller bias `β` and the wider slots `o` (`rebiasSlot_sub`). Subtracting a constant row
lowers every slot by the constant (`slot_sub_constSlots`).

Two rows of `q` slots of width `W` with entries `x + β`, `y + β'` (entries bounded by the biases)
have, in the middle slot of the product with the second row reversed, the sum
`∑ (x_t + β)(y_t + β')` (`slot_mul_eq_sum_biased`), from which the dot product `∑ x_t y_t` follows
with the two row sums (`sum_mul_eq_of_biased`), as long as `4 q β β' < 2 ^ W`. Adding
`A * 2 ^ (W * k)` to a row raises slot `k` by `A` and leaves the other slots unchanged when the
raised slot stays below `2 ^ W` (`slot_add_mul_pow_slot`).

## Implementation notes

The dot product is one product of two packed rows read at one slot. With the second row
reversed, slot `q - 1` of `X * Y` collects exactly the products of matching entries. Every slot
of the product is a sum of at most `q` products of slots, each at most `2 β · 2 β'`, so
`4 q β β' < 2 ^ W` excludes carries everywhere (`slot_mul_middle_eq_sum` of
[PackedLaurent](PackedLaurent.lean)). The biases keep every slot a natural number, and
`sum_mul_eq_of_biased` removes them afterwards with the two row sums. So `q` products of
entries cost one multiplication of two rows, one slot read and the two sums.

The biases enter that bound, which is where a smaller bias pays. `rebiasSlot` adds the new bias
`β` and subtracts `slotBias w`; the truncated subtraction is exact when the signed value is at
least `-β`, the hypothesis of `rebiasSlot_sub`. One subtraction of a constant row
(`slot_sub_constSlots`) or one addition at a single slot (`slot_add_mul_pow_slot`) is one
operation on the whole row, exact on every slot as long as no slot borrows or overflows. No
module of the library imports this one; certificates outside the library use it.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A biased slot of width `w` moved to the bias `β`. -/
def rebiasSlot (w β x : ℕ) : ℕ := Nat.sub (Nat.add x β) (slotBias w)

/-- The moved slot keeps its signed value when no subtraction truncates. -/
theorem rebiasSlot_sub {w β x : ℕ} (h : slotBias w ≤ x + β) :
    (rebiasSlot w β x : ℤ) - β = (x : ℤ) - slotBias w := by
  unfold rebiasSlot
  rw [Nat.sub_eq, Nat.add_eq]
  push_cast [h]
  ring

/-- Subtracting the constant row `c` lowers every slot by `c` when every slot is at least `c`. -/
theorem slot_sub_constSlots {W n x c : ℕ} (hW : 0 < W) (hx : x < 2 ^ (W * n))
    (hc : ∀ k < n, c ≤ slot W k x) :
    x - constSlots W n c = packSlots W n (fun k ↦ slot W k x - c) := by
  have hx' : packSlots W n (fun k ↦ slot W k x - c) + packSlots W n (fun _ ↦ c) = x := by
    rw [packSlots_add]
    conv_rhs => rw [← packSlots_slot hx]
    rw [packSlots_eq_sum, packSlots_eq_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [Nat.sub_add_cancel (hc k (mem_range.mp hk))]
  rw [constSlots_eq hW]
  omega


/-- **A dot product by one multiplication.** For rows `X`, `Y` of `q` slots of width `W` whose
slots are `x t + β` and, reversed, `y (q - 1 - t) + β'` with `|x| ≤ β`, `|y| ≤ β'`, the middle
slot of `X * Y` is `∑ₜ (xₜ + β)(yₜ + β')`. -/
theorem slot_mul_eq_sum_biased {W q β β' X Y : ℕ} {x y : ℕ → ℤ} (hX : X < 2 ^ (W * q))
    (hY : Y < 2 ^ (W * q)) (hxs : ∀ t < q, (slot W t X : ℤ) = x t + β)
    (hys : ∀ t < q, (slot W t Y : ℤ) = y (q - 1 - t) + β') (hxb : ∀ t < q, |x t| ≤ β)
    (hyb : ∀ t < q, |y t| ≤ β') (hW : q * (2 * β) * (2 * β') < 2 ^ W) :
    (slot W (q - 1) (X * Y) : ℤ) = ∑ t ∈ range q, (x t + β) * (y t + β') := by
  have hxa : ∀ t < q, slot W t X ≤ 2 * β := fun t ht ↦ by
    have h1 := hxs t ht
    have h2 := (abs_le.mp (hxb t ht)).2
    omega
  have hyb' : ∀ t < q, slot W t Y ≤ 2 * β' := fun t ht ↦ by
    have h1 := hys t ht
    have h2 := (abs_le.mp (hyb (q - 1 - t) (by omega))).2
    omega
  rw [← packSlots_slot hX, ← packSlots_slot hY, slot_mul_middle_eq_sum hxa hyb' hW]
  push_cast
  refine sum_congr rfl fun t ht ↦ ?_
  rw [mem_range] at ht
  rw [hxs t ht, hys (q - 1 - t) (by omega), show q - 1 - (q - 1 - t) = t by omega]

/-- The dot product from the biased middle slot and the two row sums. -/
theorem sum_mul_eq_of_biased {q β β' : ℕ} {x y : ℕ → ℤ} {P Sx Sy : ℤ}
    (hP : P = ∑ t ∈ range q, (x t + β) * (y t + β')) (hSx : Sx = ∑ t ∈ range q, (x t + β))
    (hSy : Sy = ∑ t ∈ range q, (y t + β')) :
    ∑ t ∈ range q, x t * y t = P - β' * Sx - β * Sy + q * β * β' := by
  rw [hP, hSx, hSy]
  simp only [mul_add, add_mul, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul,
    ← mul_sum]
  ring

/-- Adding `A` at slot `k` of a packed row whose slots stay below `2^W`. -/
theorem slot_add_mul_pow_slot {W n k A x : ℕ} (hx : x < 2 ^ (W * n)) (hk : k < n)
    (h : slot W k x + A < 2 ^ W) :
    x + A * 2 ^ (W * k) < 2 ^ (W * n) ∧ ∀ j < n,
      slot W j (x + A * 2 ^ (W * k)) = slot W j x + if j = k then A else 0 := by
  have hA : A * 2 ^ (W * k) = packSlots W n (fun j ↦ if j = k then A else 0) := by
    rw [packSlots_eq_sum, sum_eq_single k (fun j _ hj ↦ by simp [hj])
      (fun h' ↦ absurd (mem_range.mpr hk) h')]
    simp
  have hsum : x + A * 2 ^ (W * k) =
      packSlots W n (fun j ↦ slot W j x + if j = k then A else 0) := by
    rw [hA]
    conv_lhs => rw [← packSlots_slot hx]
    rw [packSlots_add]
  have hlt : ∀ j < n, slot W j x + (if j = k then A else 0) < 2 ^ W := fun j hj ↦ by
    split_ifs with hjk
    · exact hjk ▸ h
    · simpa using slot_lt W j x
  rw [hsum]
  refine ⟨packSlots_lt hlt, fun j hj ↦ ?_⟩
  rw [slot_packed_eq hlt, ite_eq_left hj]

end CAS.Numerics
