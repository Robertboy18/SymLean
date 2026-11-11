/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Numerics.PackedListComb
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Values of packed row combinations and sums of biased rows

A natural number whose integer value is the biased expansion of entries that fit is below
`2 ^ (w * n)` (`lt_two_pow_of_cast_eq`). When its entries fit, a packed row combination is that
expansion (`cast_packedRowCombination`), so it is again a row of `q` slots
(`packedRowCombination_lt`) and may enter further combinations. `biasedRowsSum w q rows` adds
biased rows, removing all but one bias row; its slots are the sums of the slots of the rows when
they fit (`signedSlot_biasedRowsSum`, with `cast_biasedRowsSum` and `biasedRowsSum_lt`). For
stored lists, `getD_of_listCheckFrom_take` reads the rows `lo` to `lo + n - 1` from a
`listCheckFrom` check of `(rows.drop lo).take n`; Mathlib's `List.getD_reverse` relates a list
stored from the last row to its reverse.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A natural number whose integer value is the biased slot expansion of entries that fit is
below `2 ^ (w * n)`. -/
theorem lt_two_pow_of_cast_eq {w n x : ℕ} {c : ℕ → ℤ} (hc : ∀ k < n, FitsSlot w (c k))
    (hx : (x : ℤ) = ∑ k ∈ range n, (c k + slotBias w) * 2 ^ (w * k)) : x < 2 ^ (w * n) := by
  have hpack : (x : ℤ) = (biasedPack w n c : ℤ) := by
    rw [hx, biasedPack, packSlots_eq_sum]
    push_cast
    exact sum_congr rfl fun j hj ↦ by rw [encodeSlot_of_fits (hc j (mem_range.mp hj))]
  exact Int.ofNat_inj.1 hpack ▸ biasedPack_lt w n c

/-- When every entry fits its slot, the packed combination is a row of `q` slots. -/
theorem packedRowCombination_lt {w q n α : ℕ} {s rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q,
      FitsSlot w (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j))) :
    packedRowCombination w q n α s rows < 2 ^ (w * q) :=
  lt_two_pow_of_cast_eq hfit (cast_packedRowCombination hrows hfit)

private theorem cast_biasedRowsSum_aux {w q : ℕ} {rows : List ℕ}
    (hrows : ∀ r ∈ rows, r < 2 ^ (w * q)) :
    (listRowSum rows : ℤ) + biasRow w q - listCount rows * biasRow w q =
      ∑ k ∈ range q, ((rows.map (signedSlot w k)).sum + slotBias w) * 2 ^ (w * k) := by
  induction rows with
  | nil =>
    change ((0 : ℕ) : ℤ) + biasRow w q - ((0 : ℕ) : ℤ) * biasRow w q = _
    rw [cast_biasRow]
    simp
  | cons r rows ih =>
    have ih' := ih fun r' hr' ↦ hrows r' (List.mem_cons_of_mem _ hr')
    change ((r + listRowSum rows : ℕ) : ℤ) + biasRow w q -
      ((listCount rows + 1 : ℕ) : ℤ) * biasRow w q = _
    have hr := cast_eq_sum_signedSlot (hrows r List.mem_cons_self)
    push_cast
    rw [hr]
    simp only [List.map_cons, List.sum_cons, add_assoc, add_mul, sum_add_distrib] at ih' ⊢
    rw [← ih', cast_biasRow]
    ring

/-- The integer value of a sum of biased rows whose slot sums fit. -/
theorem cast_biasedRowsSum {w q : ℕ} {rows : List ℕ} (hrows : ∀ r ∈ rows, r < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (rows.map (signedSlot w k)).sum) :
    (biasedRowsSum w q rows : ℤ) =
      ∑ k ∈ range q, ((rows.map (signedSlot w k)).sum + slotBias w) * 2 ^ (w * k) := by
  have h := cast_biasedRowsSum_aux hrows
  have hnn : 0 ≤ ∑ k ∈ range q, ((rows.map (signedSlot w k)).sum + slotBias w) * 2 ^ (w * k) :=
    sum_nonneg fun k hk ↦ mul_nonneg (hfit k (mem_range.mp hk)).1 (by positivity)
  have hle : listCount rows * biasRow w q ≤ listRowSum rows + biasRow w q :=
    Int.ofNat_le.1 (by push_cast; linarith)
  change ((listRowSum rows + biasRow w q - listCount rows * biasRow w q : ℕ) : ℤ) = _
  rw [Nat.cast_sub hle]
  push_cast
  exact h

/-- **Sums of biased rows.** The slots of `biasedRowsSum` are the sums of the slots of the rows,
when they fit. -/
theorem signedSlot_biasedRowsSum {w q : ℕ} {rows : List ℕ} (hrows : ∀ r ∈ rows, r < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (rows.map (signedSlot w k)).sum) {k : ℕ} (hk : k < q) :
    signedSlot w k (biasedRowsSum w q rows) = (rows.map (signedSlot w k)).sum :=
  signedSlot_eq_of_cast_eq hfit (cast_biasedRowsSum hrows hfit) hk

/-- If every row is below `2 ^ (w * q)` and the sum of the signed slots `k` of the rows fits for
every `k < q`, then `biasedRowsSum w q rows` is again a row below `2 ^ (w * q)`. -/
theorem biasedRowsSum_lt {w q : ℕ} {rows : List ℕ} (hrows : ∀ r ∈ rows, r < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (rows.map (signedSlot w k)).sum) :
    biasedRowsSum w q rows < 2 ^ (w * q) :=
  lt_two_pow_of_cast_eq hfit (cast_biasedRowsSum hrows hfit)

/-- A list check of the rows `lo` to `lo + n - 1` of a stored list: each of them is `f` of its
index and passes `g`. -/
theorem getD_of_listCheckFrom_take {f : ℕ → ℕ} {g : ℕ → Bool} {lo n : ℕ} {rows : List ℕ}
    (h : listCheckFrom f g lo ((rows.drop lo).take n) = true) {k : ℕ} (hlo : lo ≤ k)
    (hk : k < lo + n) (hlen : k < rows.length) :
    rows.getD k 0 = f k ∧ g (rows.getD k 0) = true := by
  have hl : k - lo < ((rows.drop lo).take n).length := by
    simp only [List.length_take, List.length_drop]; omega
  have hget : ((rows.drop lo).take n).getD (k - lo) 0 = rows.getD k 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_eq_left (by omega), Nat.add_sub_cancel' hlo]
  have := listCheckFrom_spec h hl
  rwa [hget, Nat.add_sub_cancel' hlo] at this

end CAS.Numerics
