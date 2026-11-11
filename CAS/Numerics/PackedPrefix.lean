/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots

/-!
# Prefix sums in one packed row

`prefixPack w n f` holds the prefix sums `f 0 + ⋯ + f i`, `i < n`, in slots of width `w`; slot
`i` is the prefix sum ending at `f i` when every prefix sum fits a slot (`slot_prefixPack`).

## Implementation notes

We build the row in one pass. `prefixPackState` is a `Nat.rec` whose state is the pair of the
running sum and the packed row; step `i` adds `f i` to the running sum and adds the new sum,
shifted left by `w i`, to the row. The `n` prefix sums thus cost `n` additions to the running
sum and `n` shifts and additions on the row, where computing each prefix sum on its own would
cost `n (n - 1) / 2` additions; a kernel loop then reads each of them by slot extraction.
`prefixPackState_eq` identifies the state with the two sums in closed form; the shifted entries
never overlap once every prefix sum is below `2 ^ w`, the only hypothesis of `slot_prefixPack`.
No module of the library imports this one; certificates outside the library use it.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The running sum and the packed prefix sums after `n` steps. -/
def prefixPackState (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ × ℕ) (0, 0)
    (fun i p ↦ (Nat.add p.1 (f i), Nat.add p.2 (Nat.shiftLeft (Nat.add p.1 (f i)) (Nat.mul w i))))
    n

/-- The prefix sums `f 0 + ⋯ + f i`, `i < n`, in slots of width `w`. -/
def prefixPack (w n : ℕ) (f : ℕ → ℕ) : ℕ := (prefixPackState w f n).2

/-- After `n` steps the state is the pair of `∑ k ∈ range n, f k` and the packing in slots of
width `w` of the prefix sums `∑ k ∈ range (i + 1), f k` for `i < n`, for entries of any size. -/
theorem prefixPackState_eq (w : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    prefixPackState w f n = (∑ k ∈ range n, f k,
      packSlots w n fun i ↦ ∑ k ∈ range (i + 1), f k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Nat.add (prefixPackState w f n).1 (f n), Nat.add (prefixPackState w f n).2
      (Nat.shiftLeft (Nat.add (prefixPackState w f n).1 (f n)) (Nat.mul w n))) = _
    rw [ih, packSlots_succ, sum_range_succ]
    simp only [Nat.add_eq, Nat.mul_eq,
      show ∀ a b : ℕ, Nat.shiftLeft a b = a * 2 ^ b from Nat.shiftLeft_eq]

/-- Slot `i` of the packed prefix sums is the prefix sum, when every prefix sum fits. -/
theorem slot_prefixPack {w n : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, ∑ k ∈ range (i + 1), f k < 2 ^ w)
    {i : ℕ} (hi : i < n) : slot w i (prefixPack w n f) = ∑ k ∈ range (i + 1), f k := by
  rw [prefixPack, prefixPackState_eq, slot_packed_eq h i,
    ite_eq_left_iff.mpr (fun h' ↦ absurd hi h')]

end CAS.Numerics
