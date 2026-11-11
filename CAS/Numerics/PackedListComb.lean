/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Numerics.PackedLinearAlgebra
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.ModEq

/-!
# Packed row combinations over a stored list of rows

The rows `R_0, …, R_{n-1}` are stored as the list `[R_{n-1}, …, R_0]`. `packedRevComb w q n α s
rows rs` is `packedRowCombination` over them, the row `R_j` taking the scalar `s j`, when `rs` is
the stored sum of the rows (`packedRevComb_eq`).

`packedSlotComb w q n α W S rows rs` does the same over rows stored from the first, with the
slots of width `W` of one packed number `S` as the scalars: `slotDot` reads them by shifting `S`
down one slot per row, and their sum is the one remainder `S mod (2 ^ W - 1)`
(`packedSlotComb_eq`, by `mod_two_pow_sub_one_eq` when the sum of the slots is below
`2 ^ W - 1`). `biasedRowsSum` sums biased rows and keeps the bias row once, and
`listCheckFrom f g i rows` checks that every stored row is `f` of its index and passes `g`
(`listCheckFrom_spec`).

## Implementation notes

Certificates hold their rows as lists, and we walk each list once instead of looking rows up by
index, which with `rows.getD j 0` inside `natSum` would walk the list again for every `j`.
`revDot` is a `Nat.rec` on the count `n` whose motive is a function of the list: the step for
`k + 1` takes the head with the scalar `s k` and passes the tail on. So the kernel walks the
list once by the recursor of the count, and the index of every step is a literal; the rows are
stored from the last because the outermost step has the index `n - 1`. Each row costs one
product and one addition, and `packedRevComb` adds the bias terms of `packedRowCombination`,
with the sum `rs` of the rows as an argument that the theorems take as `listRowSum rows`.
`packedRevComb_eq` holds for every list of length `n`, so the soundness is that of
[PackedLinearAlgebra](PackedLinearAlgebra.lean).

`slotDot` is a `List.rec` over rows stored from the first that carries all scalars as one
number, reading the low slot with an `and` against `slotMask W`. The bias term needs the sum of
the scalars, and one remainder gives it since `2 ^ W ≡ 1` modulo `2 ^ W - 1`: `S` is congruent
to the sum of its slots (`packSlots_modEq`), as in `zPosSum` of
[PackedSignedRows](PackedSignedRows.lean). The sum must stay below `2 ^ W - 1` and `S` below
`2 ^ (W n)`, the hypotheses of `packedSlotComb_eq`. `listCheckFrom`
checks a stored list against a generating function in the same single pass, carrying the index.
[PackedRowSums](PackedRowSums.lean) proves the slots of `biasedRowsSum`
(`signedSlot_biasedRowsSum`) and reads rows from `listCheckFrom`; certificates outside the
library use the combinations and the checks.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- `∑_{j < n} s j R_j` over the rows stored from the last, `rows = [R_{n-1}, …, R_0]`. -/
def revDot (s : ℕ → ℕ) (n : ℕ) (rows : List ℕ) : ℕ :=
  Nat.rec (motive := fun _ ↦ List ℕ → ℕ) (fun _ ↦ 0)
    (fun k ih rs ↦ List.casesOn (motive := fun _ ↦ ℕ) rs 0
      (fun r tl ↦ Nat.add (Nat.mul (s k) r) (ih tl))) n rows

/-- The sum of the rows. -/
def listRowSum (rows : List ℕ) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun r _ ih ↦ Nat.add r ih) rows

/-- The number of rows. -/
def listCount (rows : List ℕ) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun _ _ ih ↦ Nat.succ ih) rows

/-- `packedRowCombination` over the `n` rows stored from the last, given their sum `rs`. -/
def packedRevComb (w q n α : ℕ) (s : ℕ → ℕ) (rows : List ℕ) (rs : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (revDot s n rows) (Nat.mul (Nat.add (Nat.mul n α) 1) (biasRow w q)))
    (Nat.add (Nat.mul α rs) (Nat.mul (natSum n s) (biasRow w q)))

/-- `∑_l slot W l S · R_l` over the rows stored from the first, the slots of `S` read by shifting
it down one slot per row. -/
def slotDot (W S : ℕ) (rows : List ℕ) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ → ℕ) (fun _ ↦ 0)
    (fun r _ ih x ↦ Nat.add (Nat.mul (Nat.land x (slotMask W)) r) (ih (Nat.shiftRight x W))) rows S

/-- `packedRowCombination` over the `n` rows stored from the first, the scalars the slots of
width `W` of `S` and their sum read as `S mod (2^W - 1)`, given the sum `rs` of the rows. -/
def packedSlotComb (w q n α W S : ℕ) (rows : List ℕ) (rs : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (slotDot W S rows) (Nat.mul (Nat.add (Nat.mul n α) 1) (biasRow w q)))
    (Nat.add (Nat.mul α rs) (Nat.mul (Nat.mod S (Nat.sub (2 ^ W) 1)) (biasRow w q)))

/-- The sum of biased rows `∑ r - (n - 1) H`, with the bias row `H` once. -/
def biasedRowsSum (w q : ℕ) (rows : List ℕ) : ℕ :=
  Nat.sub (Nat.add (listRowSum rows) (biasRow w q)) (Nat.mul (listCount rows) (biasRow w q))

/-- For a list of length `n`, `revDot s n rows` is `∑ j ∈ range n, s j * rows.getD (n - 1 - j) 0`:
row `j` is stored at position `n - 1 - j`. -/
theorem revDot_eq (s : ℕ → ℕ) {n : ℕ} {rows : List ℕ} (h : rows.length = n) :
    revDot s n rows = ∑ j ∈ range n, s j * rows.getD (n - 1 - j) 0 := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    obtain _ | ⟨r, tl⟩ := rows
    · simp at h
    have htl : tl.length = n := by simpa using h
    change s n * r + revDot s n tl = _
    rw [ih htl, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero, add_comm]
    congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    rw [show n - j = (n - 1 - j) + 1 by have := mem_range.mp hj; omega, List.getD_cons_succ]

/-- `listRowSum rows` is the sum of `rows.getD j 0` over `j < rows.length`. -/
theorem listRowSum_eq (rows : List ℕ) :
    listRowSum rows = ∑ j ∈ range rows.length, rows.getD j 0 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    change r + listRowSum rows = _
    rw [ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

/-- `slotDot W S rows` is `∑ l ∈ range rows.length, slot W l S * rows.getD l 0`. -/
theorem slotDot_eq (W S : ℕ) (rows : List ℕ) :
    slotDot W S rows = ∑ l ∈ range rows.length, slot W l S * rows.getD l 0 := by
  induction rows generalizing S with
  | nil => rfl
  | cons r rows ih =>
    change Nat.land S (slotMask W) * r + slotDot W (S >>> W) rows = _
    rw [ih, List.length_cons, sum_range_succ', List.getD_cons_zero, add_comm]
    congr 1
    refine sum_congr rfl fun l _ ↦ ?_
    rw [List.getD_cons_succ, slot_eq, slot_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← pow_add, show W + W * l = W * (l + 1) by rw [Nat.mul_succ, Nat.add_comm]]

/-- A packing in slots of width `W` is congruent modulo `2 ^ W - 1` to the sum of its entries,
for entries of any size. -/
theorem packSlots_modEq (W n : ℕ) (f : ℕ → ℕ) :
    Nat.ModEq (2 ^ W - 1) (packSlots W n f) (∑ l ∈ range n, f l) := by
  have h2 : Nat.ModEq (2 ^ W - 1) (2 ^ W) 1 := Nat.modEq_sub Nat.one_le_two_pow
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [packSlots_succ, sum_range_succ]
    have h : Nat.ModEq (2 ^ W - 1) (2 ^ (W * n)) 1 := by
      rw [pow_mul]; simpa using h2.pow n
    exact ih.add (by simpa using h.mul_left (f n))

/-- A packed row is its sum of slots modulo `2^W - 1`, when that sum is smaller. -/
theorem mod_two_pow_sub_one_eq {W n x : ℕ} (hx : x < 2 ^ (W * n))
    (hsum : ∑ l ∈ range n, slot W l x < 2 ^ W - 1) :
    x % (2 ^ W - 1) = ∑ l ∈ range n, slot W l x := by
  have := packSlots_modEq W n (fun l ↦ slot W l x)
  rw [packSlots_slot hx] at this
  rw [this, Nat.mod_eq_of_lt hsum]

/-- **The slot combination** is the packed combination of the rows `R_l = rows[l]` with the
scalars the slots of `S`. -/
theorem packedSlotComb_eq (w q α W : ℕ) {S n : ℕ} {rows : List ℕ} (h : rows.length = n)
    (hS : S < 2 ^ (W * n)) (hsum : ∑ l ∈ range n, slot W l S < 2 ^ W - 1) :
    packedSlotComb w q n α W S rows (listRowSum rows) =
      packedRowCombination w q n α (fun l ↦ slot W l S) (fun l ↦ rows.getD l 0) := by
  simp only [packedSlotComb, packedRowCombination, slotDot_eq, listRowSum_eq, natSum_eq_sum, h]
  rw [show Nat.mod S (Nat.sub (2 ^ W) 1) = S % (2 ^ W - 1) from rfl,
    mod_two_pow_sub_one_eq hS hsum]
  rfl

/-- **The list combination** is the packed combination of the rows `R_j = rows[n - 1 - j]`. -/
theorem packedRevComb_eq (w q α : ℕ) (s : ℕ → ℕ) {n : ℕ} {rows : List ℕ} (h : rows.length = n) :
    packedRevComb w q n α s rows (listRowSum rows) =
      packedRowCombination w q n α s (fun j ↦ rows.getD (n - 1 - j) 0) := by
  have hsum : listRowSum rows = natSum n fun j ↦ rows.getD (n - 1 - j) 0 := by
    rw [listRowSum_eq, natSum_eq_sum, h]
    exact (Finset.sum_range_reflect (fun j ↦ rows.getD j 0) n).symm
  simp only [packedRevComb, packedRowCombination, revDot_eq s h, hsum, natSum_eq_sum]
  rfl

/-- Every row of the list is `f` of its index counted from `i`, and passes `g`. -/
def listCheckFrom (f : ℕ → ℕ) (g : ℕ → Bool) (i : ℕ) (rows : List ℕ) : Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun _ ↦ true)
    (fun r _ ih i ↦ Nat.beq r (f i) && g r && ih (Nat.succ i)) rows i

/-- If `listCheckFrom f g i rows` holds, every row at a position `k < rows.length` is `f (i + k)`
and passes `g`. -/
theorem listCheckFrom_spec {f : ℕ → ℕ} {g : ℕ → Bool} {i : ℕ} {rows : List ℕ}
    (h : listCheckFrom f g i rows = true) {k : ℕ} (hk : k < rows.length) :
    rows.getD k 0 = f (i + k) ∧ g (rows.getD k 0) = true := by
  induction rows generalizing i k with
  | nil => simp at hk
  | cons r rows ih =>
    change (Nat.beq r (f i) && g r && listCheckFrom f g (i + 1) rows) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    rcases k with _ | k
    · exact ⟨by simpa using h.1.1, by simpa using h.1.2⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1 k] using ih h.2 (k := k) (by simpa using hk)

end CAS.Numerics
