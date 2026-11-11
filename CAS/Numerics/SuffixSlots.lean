/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Binary64Grid
public import CAS.Numerics.MatrixPositivity
public import CAS.Numerics.PackedWindows

/-!
# Suffix sums of binary64 words in packed slots

A column of binary64 words `g 0, g 1, …` is stored by its suffix sums `σ r = ∑_{m ≥ r} g m`
on the grid with `p` fractional bits, as biased slots of width `w`. `suffixWordCheck` checks one
word against two consecutive slots with natural-number operations only: the decoding is exact,
its magnitude is at most a bound, and slot `r` minus slot `r + 1` is the signed grid numerator
(`signedSlot_sub_of_suffixWordCheck`). A passing check also gives the exact value of the word
(`binary64DyadicValue_eq_of_suffixWordCheck`). Consecutive differences and a vanishing top slot
determine every slot as a sum of differences (`eq_sum_Ico_of_sub_eq`).

A table of `rows × cols` words, read as rows of 64-bit slots `words m`, is stored as `cols`
columns `col l` of `rows + 9` slots: slot `r` holds `∑_{m ≥ r - 3} g m l`, so the three bottom
slots repeat the total and the slots from `rows + 3` on are zero. `suffixBlockCheck` checks the
words of the rows `64 b, …, 64 b + 63` of every column against one window of the column, and
`suffixPaddingCheck` checks the padding slots of a column; together they give every slot
(`signedSlot_eq_sum_of_suffixChecks`) and the exact value of every word
(`binary64DyadicValue_eq_of_suffixChecks`).

## Implementation notes

Untrusted code computes the suffix sums and stores the columns; the kernel checks them. With
suffix sums, every word is decoded to its grid numerator and compared with the difference of two
adjacent slots; the sign bit decides which of the two slots gets the magnitude added, so the
comparison is one addition and one equality test of natural numbers. A slot then holds the tail
sum from its row on, which `eq_sum_Ico_of_sub_eq` recovers by telescoping from the zero top
slot. `slotWindow` cuts the 65 slots of a block of 64 rows out of the column once, so that each
word reads its slots from a short number.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- Slot `r` of `x` minus slot `r + 1` is the exact grid numerator of `word`, whose magnitude
is at most `bound`. -/
def suffixWordCheck (w p bound x r word : ℕ) : Bool :=
  binary64GridExact p word &&
    Nat.ble (decodeWordToGridMagnitude p word) bound &&
    cond (Nat.beq (binary64SignBit word) 0)
      (Nat.beq (slot w r x) (Nat.add (slot w (r + 1) x) (decodeWordToGridMagnitude p word)))
      (Nat.beq (Nat.add (slot w r x) (decodeWordToGridMagnitude p word)) (slot w (r + 1) x))

/-- A passing `suffixWordCheck w p bound x r word` makes signed slot `r` of `x` minus signed slot
`r + 1` the grid numerator `decodeWordToGrid p word`. -/
theorem signedSlot_sub_of_suffixWordCheck {w p bound x r word : ℕ}
    (h : suffixWordCheck w p bound x r word = true) :
    signedSlot w r x - signedSlot w (r + 1) x = decodeWordToGrid p word := by
  simp only [suffixWordCheck, Bool.and_eq_true] at h
  obtain ⟨_, hc⟩ := h
  rw [signedSlot, signedSlot, decodeWordToGrid_eq]
  by_cases hs : binary64SignBit word = 0
  · rw [show Nat.beq (binary64SignBit word) 0 = true from Nat.beq_eq.mpr hs, Bool.cond_true] at hc
    rw [ite_eq_left hs, Nat.eq_of_beq_eq_true hc, Nat.add_eq]
    push_cast
    ring
  · rw [show Nat.beq (binary64SignBit word) 0 = false from
      Bool.eq_false_iff.mpr fun e ↦ hs (Nat.eq_of_beq_eq_true e), Bool.cond_false] at hc
    rw [ite_eq_right hs, ← Nat.eq_of_beq_eq_true hc, Nat.add_eq]
    push_cast
    ring

/-- A passing `suffixWordCheck w p bound x r word` bounds `|decodeWordToGrid p word|` by
`bound`. -/
theorem natAbs_decodeWordToGrid_le_of_suffixWordCheck {w p bound x r word : ℕ}
    (h : suffixWordCheck w p bound x r word = true) :
    (decodeWordToGrid p word).natAbs ≤ bound := by
  simp only [suffixWordCheck, Bool.and_eq_true] at h
  have hle := Nat.le_of_ble_eq_true h.1.2
  rw [decodeWordToGrid_eq]
  split_ifs <;> simpa using hle

/-- A passing `suffixWordCheck w p bound x r word` gives the exact value of the word:
`binary64DyadicValue word = decodeWordToGrid p word / 2 ^ p`. -/
theorem binary64DyadicValue_eq_of_suffixWordCheck {w p bound x r word : ℕ}
    (h : suffixWordCheck w p bound x r word = true) :
    binary64DyadicValue word = (decodeWordToGrid p word : ℚ) / 2 ^ p := by
  simp only [suffixWordCheck, Bool.and_eq_true] at h
  rw [decodeWordToGrid_exact h.1.1]
  field_simp

/-- Values with prescribed consecutive differences on `[a, n)` and `f n = 0` are the sums of
the differences up to `n`. -/
theorem eq_sum_Ico_of_sub_eq {f d : ℕ → ℤ} {a n : ℕ}
    (hd : ∀ r, a ≤ r → r < n → f r - f (r + 1) = d r) (hn : f n = 0) :
    ∀ r, a ≤ r → r ≤ n → f r = ∑ k ∈ Ico r n, d k := by
  have key : ∀ t r, r + t = n → a ≤ r → f r = ∑ k ∈ Ico r n, d k := by
    intro t
    induction t with
    | zero => intro r hr _; subst hr; simpa using hn
    | succ t ih =>
      intro r hr har
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ← ih (r + 1) (by omega) (by omega)]
      linarith [hd r har (by omega)]
  exact fun r har hrn ↦ key (n - r) r (by omega) har

/-- Slots whose consecutive differences below `n` are `g (r - o)` for `o ≤ r` and `0` for
`r < o`, with slot `n` zero, hold the suffix sums `∑_{m ∈ [r - o, top)} g m` of a column `g`
vanishing from `top` on: `o` padding slots at the bottom repeat the total. -/
theorem signedSlot_eq_sum_Ico_of_sub_eq {w x o top n : ℕ} {g : ℕ → ℤ}
    (hg : ∀ m, top ≤ m → g m = 0) (htop : top + o ≤ n)
    (hd : ∀ r < n, signedSlot w r x - signedSlot w (r + 1) x = if o ≤ r then g (r - o) else 0)
    (hn : signedSlot w n x = 0) {r : ℕ} (hr : r ≤ n) :
    signedSlot w r x = ∑ m ∈ Ico (r - o) top, g m := by
  rw [eq_sum_Ico_of_sub_eq (a := 0) (fun r _ hr ↦ hd r hr) hn r (Nat.zero_le r) hr]
  have hsplit : ∑ k ∈ Ico r n, (if o ≤ k then g (k - o) else 0) =
      ∑ k ∈ Ico (max r o) n, g (k - o) := by
    rcases le_total o r with h | h
    · rw [max_eq_left h]
      exact sum_congr rfl fun k hk ↦ by rw [ite_eq_left (le_trans h (mem_Ico.mp hk).1)]
    · rw [max_eq_right h, ← sum_Ico_consecutive _ h (by omega)]
      rw [sum_eq_zero fun k hk ↦ by rw [ite_eq_right (by have := (mem_Ico.mp hk).2; omega)],
        zero_add]
      exact sum_congr rfl fun k hk ↦ by rw [ite_eq_left (mem_Ico.mp hk).1]
  rw [hsplit]
  have hshift : ∑ k ∈ Ico (max r o) n, g (k - o) = ∑ m ∈ Ico (r - o) (n - o), g m := by
    have h1 : max r o = (r - o) + o := by omega
    have h2 : n = (n - o) + o := by omega
    rw [h1, h2, ← sum_Ico_add']
    simp only [Nat.add_sub_cancel]
  rw [hshift]
  rcases le_or_gt (r - o) top with h | h
  · rw [← sum_Ico_consecutive _ h (by omega : top ≤ n - o)]
    rw [sum_eq_zero (s := Ico top (n - o)) fun m hm ↦ hg m (mem_Ico.mp hm).1, add_zero]
  · rw [Ico_eq_empty_of_le h.le, sum_empty]
    exact sum_eq_zero fun m hm ↦ hg m (by have := (mem_Ico.mp hm).1; omega)

/-- The slots `o, …, o + n - 1` of `x` as a packed number. -/
def slotWindow (w o n x : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight x (Nat.mul w o)) (slotMask (Nat.mul w n))

/-- For `j < n`, slot `j` of `slotWindow w o n x` is slot `j + o` of `x`. -/
theorem slot_slotWindow {w o n j : ℕ} (hj : j < n) (x : ℕ) :
    slot w j (slotWindow w o n x) = slot w (j + o) x := by
  rw [slotWindow, slot_window hj]

/-- For `j < n`, signed slot `j` of `slotWindow w o n x` is signed slot `j + o` of `x`. -/
theorem signedSlot_slotWindow {w o n j : ℕ} (hj : j < n) (x : ℕ) :
    signedSlot w j (slotWindow w o n x) = signedSlot w (j + o) x := by
  rw [signedSlot, signedSlot, slotWindow, slot_window hj]

/-- The words of the rows `64 b + k < rows` of every column `l < cols` against the window of the
slots `64 b + 3, …, 64 b + 67` of the column. -/
def suffixBlockCheck (w p bound rows cols : ℕ) (col words : ℕ → ℕ) (b : ℕ) : Bool :=
  natAll cols fun l ↦
    let win := slotWindow w (64 * b + 3) 65 (col l)
    natAll 64 fun k ↦
      Nat.ble rows (64 * b + k) || suffixWordCheck w p bound win k (slot 64 l (words (64 * b + k)))

/-- The three bottom slots repeat the next one, the slots `rows + 3, …, rows + 8` repeat the
top slot, which is zero. -/
def suffixPaddingCheck (w rows x : ℕ) : Bool :=
  natAll 3 (fun r ↦ Nat.beq (slot w r x) (slot w (r + 1) x)) &&
    natAll 5 (fun r ↦ Nat.beq (slot w (rows + 3 + r) x) (slot w (rows + 4 + r) x)) &&
    Nat.beq (slot w (rows + 8) x) (slotBias w)

/-- If `suffixBlockCheck` passes for every block `b < (rows + 63) / 64`, then for `m < rows` and
`l < cols` the word `slot 64 l (words m)` passes `suffixWordCheck` at slot `m % 64` of the window
of its block in column `l`. -/
theorem suffixWordCheck_of_suffixBlockCheck {w p bound rows cols : ℕ} {col words : ℕ → ℕ}
    (h : ∀ b < (rows + 63) / 64, suffixBlockCheck w p bound rows cols col words b = true)
    {m l : ℕ} (hm : m < rows) (hl : l < cols) :
    suffixWordCheck w p bound (slotWindow w (64 * (m / 64) + 3) 65 (col l)) (m % 64)
      (slot 64 l (words m)) = true := by
  have hb := natAll_spec (natAll_spec (h (m / 64) (by omega)) hl) (Nat.mod_lt m (by norm_num))
  rw [show 64 * (m / 64) + m % 64 = m from Nat.div_add_mod m 64, Bool.or_eq_true] at hb
  exact hb.resolve_left fun h' ↦ absurd (Nat.le_of_ble_eq_true h') (by omega)

/-- If `suffixBlockCheck` passes for every block `b < (rows + 63) / 64`, then for `m < rows` and
`l < cols` signed slot `m + 3` of `col l` minus signed slot `m + 4` is the grid numerator
`decodeWordToGrid p (slot 64 l (words m))`. -/
theorem signedSlot_sub_of_suffixBlockCheck {w p bound rows cols : ℕ} {col words : ℕ → ℕ}
    (h : ∀ b < (rows + 63) / 64, suffixBlockCheck w p bound rows cols col words b = true)
    {m l : ℕ} (hm : m < rows) (hl : l < cols) :
    signedSlot w (m + 3) (col l) - signedSlot w (m + 3 + 1) (col l) =
      decodeWordToGrid p (slot 64 l (words m)) := by
  have hc := suffixWordCheck_of_suffixBlockCheck h hm hl
  rw [← signedSlot_sub_of_suffixWordCheck hc, signedSlot_slotWindow (by omega),
    signedSlot_slotWindow (by omega)]
  congr 2 <;> omega

/-- Every slot of a checked column is a suffix sum of the grid numerators of its words. -/
theorem signedSlot_eq_sum_of_suffixChecks {w p bound rows cols : ℕ} {col words : ℕ → ℕ}
    (h : ∀ b < (rows + 63) / 64, suffixBlockCheck w p bound rows cols col words b = true)
    (hpad : ∀ l < cols, suffixPaddingCheck w rows (col l) = true) {l r : ℕ} (hl : l < cols)
    (hr : r ≤ rows + 8) :
    signedSlot w r (col l) = ∑ m ∈ Ico (r - 3) rows,
      (if m < rows then decodeWordToGrid p (slot 64 l (words m)) else 0) := by
  have hp := hpad l hl
  simp only [suffixPaddingCheck, Bool.and_eq_true] at hp
  obtain ⟨⟨hlow, hhigh⟩, htop⟩ := hp
  apply signedSlot_eq_sum_Ico_of_sub_eq (fun m hm ↦ ite_eq_right (by omega)) (by omega) _ _ hr
  · intro r hr
    split_ifs with h3 hrow
    · have := signedSlot_sub_of_suffixBlockCheck h hrow hl
      rwa [show r - 3 + 3 = r by omega] at this
    · have he := Nat.eq_of_beq_eq_true (natAll_spec hhigh (show r - (rows + 3) < 5 by omega))
      rw [show rows + 3 + (r - (rows + 3)) = r by omega,
        show rows + 4 + (r - (rows + 3)) = r + 1 by omega] at he
      rw [signedSlot, signedSlot, he, sub_self]
    · have he := Nat.eq_of_beq_eq_true (natAll_spec hlow (show r < 3 by omega))
      rw [signedSlot, signedSlot, he, sub_self]
  · rw [signedSlot, Nat.eq_of_beq_eq_true htop, sub_self]

/-- If `suffixBlockCheck` passes for every block `b < (rows + 63) / 64`, then for `m < rows` and
`l < cols` the word `slot 64 l (words m)` has the exact value of its grid numerator over
`2 ^ p`. -/
theorem binary64DyadicValue_eq_of_suffixChecks {w p bound rows cols : ℕ} {col words : ℕ → ℕ}
    (h : ∀ b < (rows + 63) / 64, suffixBlockCheck w p bound rows cols col words b = true)
    {m l : ℕ} (hm : m < rows) (hl : l < cols) :
    binary64DyadicValue (slot 64 l (words m)) =
      (decodeWordToGrid p (slot 64 l (words m)) : ℚ) / 2 ^ p :=
  binary64DyadicValue_eq_of_suffixWordCheck (suffixWordCheck_of_suffixBlockCheck h hm hl)

/-- If `suffixBlockCheck` passes for every block `b < (rows + 63) / 64`, then for `m < rows` and
`l < cols` the grid numerator of the word `slot 64 l (words m)` is at most `bound` in absolute
value. -/
theorem natAbs_decodeWordToGrid_le_of_suffixChecks {w p bound rows cols : ℕ}
    {col words : ℕ → ℕ}
    (h : ∀ b < (rows + 63) / 64, suffixBlockCheck w p bound rows cols col words b = true)
    {m l : ℕ} (hm : m < rows) (hl : l < cols) :
    (decodeWordToGrid p (slot 64 l (words m))).natAbs ≤ bound :=
  natAbs_decodeWordToGrid_le_of_suffixWordCheck (suffixWordCheck_of_suffixBlockCheck h hm hl)

end CAS.Numerics
