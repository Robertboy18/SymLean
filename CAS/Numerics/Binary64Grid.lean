/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# Binary64 words on a binary fixed-point grid

`decodeWordToGrid precision word` reads the sign, exponent and fraction fields of a binary64
word with shifts and masks and returns the integer `n` with `n / 2 ^ precision` closest to the
encoded value from the side of zero: with `E` the biased exponent, or one for a subnormal
(`binary64ScaleExponent`), the significand is shifted left by `precision + E - 1075` when this
is nonnegative and shifted right by `1075 - precision - E` otherwise. No rational number is
formed. `decodeWordToGrid_sound` bounds the error by one grid unit, and when
`binary64GridExact precision word` holds, so that the shift drops no nonzero bit, the decoding
is exact (`decodeWordToGrid_exact`): the word is the grid value `BinaryGrid.toRat precision n`
(`binary64DyadicValue_eq_toRat`), which is `n / 2 ^ precision` (`binaryGrid_toRat_eq_div`).
Infinite and NaN encodings decode to zero, as in `binary64DyadicValue`.

A table of words is decoded once into a packed table of grid numerators: the finite check
`gridSlotCheck` compares a stored biased slot with the shift decoding of its word, checks
`binary64GridExact` and rejects infinite and NaN encodings, with a few natural-number
operations per word, and
`binary64DyadicValue_eq_toRat_of_gridSlotCheck` turns a passing check into the exact value of
the word as the grid value of the stored entry. The packed numerators are reused afterwards.
For tables stored as rows, `gridRowCheck` runs `gridSlotCheck` on every word of a row of
64-bit slots against the row of grid numerators, so a table needs one lookup per row in each
table (`binary64DyadicValue_slot_eq_toRat_of_gridRowCheck`). `gridSlotTruncCheck` and
`gridRowTruncCheck` drop the exactness test, for words whose values need not lie on the grid; a
passing check puts the value of the word within one grid step of the stored entry
(`abs_binary64DyadicValue_sub_signedSlot_le`).

## Implementation notes

We store a table of binary64 inputs as grid numerators, natural numbers with a bias in the
slots of one packed literal, so that later computations work on integers at one fixed
precision, as the suffix sums of `CAS.Numerics.SuffixSlots` do. The kernel never decodes a word
to a rational: a check redoes the shift decoding and compares it with the stored slot, a few
natural-number operations per word, and the theorems turn a passing check into the exact or
truncated value of the word.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The grid values
  `FloatLib.Numerics.Interval.BinaryGrid.toRat`.
* IEEE Computer Society, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, IEEE,
  Piscataway, NJ, 2019, <https://doi.org/10.1109/IEEESTD.2019.8766229>. The binary64
  interchange format.
-/

@[expose] public section

namespace CAS.Numerics

/-- The fifty-two fraction bits of a binary64 word. -/
def binary64FractionField (word : ℕ) : ℕ := Nat.land word (slotMask 52)

/-- The sign bit of a binary64 word. -/
def binary64SignBit (word : ℕ) : ℕ := Nat.land (Nat.shiftRight word 63) 1

/-- The integer significand: the fraction with the hidden bit for normal numbers. -/
def binary64Significand (word : ℕ) : ℕ :=
  cond (Nat.beq (binary64ExponentField word) 0) (binary64FractionField word)
    (Nat.add (Nat.shiftLeft 1 52) (binary64FractionField word))

/-- The exponent `e` with value `significand * 2 ^ (e - 1075)`: the exponent field, or one for
subnormal numbers. -/
def binary64ScaleExponent (word : ℕ) : ℕ :=
  cond (Nat.beq (binary64ExponentField word) 0) 1 (binary64ExponentField word)

/-- The scaled value is `significand * 2 ^ (binary64GridShift precision word - 1075)`. -/
def binary64GridShift (precision word : ℕ) : ℕ :=
  Nat.add precision (binary64ScaleExponent word)

/-- The magnitude on the grid with `precision` fractional bits, rounded toward zero. -/
def decodeWordToGridMagnitude (precision word : ℕ) : ℕ :=
  cond (Nat.beq (binary64ExponentField word) 2047) 0
    (cond (Nat.ble 1075 (binary64GridShift precision word))
      (Nat.shiftLeft (binary64Significand word) (Nat.sub (binary64GridShift precision word) 1075))
      (Nat.shiftRight (binary64Significand word)
        (Nat.sub 1075 (binary64GridShift precision word))))

/-- The grid numerator of a binary64 word with `precision` fractional bits, rounded toward
zero. -/
def decodeWordToGrid (precision word : ℕ) : ℤ :=
  cond (Nat.beq (binary64SignBit word) 0) (decodeWordToGridMagnitude precision word)
    (-(decodeWordToGridMagnitude precision word : ℤ))

/-- Whether `decodeWordToGrid precision word` is exact (`decodeWordToGrid_exact`): true when the
exponent field is `2047` (the word decodes to zero), when `1075 ≤ binary64GridShift precision word`
(a left shift), or when the significand has no nonzero bit below position
`1075 - binary64GridShift precision word`. -/
def binary64GridExact (precision word : ℕ) : Bool :=
  Nat.beq (binary64ExponentField word) 2047 ||
    Nat.ble 1075 (binary64GridShift precision word) ||
    Nat.beq (Nat.land (binary64Significand word)
      (slotMask (Nat.sub 1075 (binary64GridShift precision word)))) 0

/-- The fraction field is the word modulo `2 ^ 52`. -/
theorem binary64FractionField_eq (word : ℕ) : binary64FractionField word = word % 2 ^ 52 := by
  change word &&& slotMask 52 = _
  rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod]

/-- The sign bit is bit 63 of the word, as a quotient and a remainder. -/
theorem binary64SignBit_eq (word : ℕ) : binary64SignBit word = word / 2 ^ 63 % 2 := by
  change (word >>> 63) &&& (2 ^ 1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_one]

/-- The significand is the fraction `word % 2 ^ 52` when the exponent field is zero, and
`2 ^ 52` plus the fraction otherwise. -/
theorem binary64Significand_eq (word : ℕ) : binary64Significand word =
    if binary64ExponentField word = 0 then word % 2 ^ 52 else 2 ^ 52 + word % 2 ^ 52 := by
  simp only [binary64Significand, cond_eq_ite, Nat.beq_eq, binary64FractionField_eq]
  rfl

/-- The scale exponent is one when the exponent field is zero, and the exponent field
otherwise. -/
theorem binary64ScaleExponent_eq (word : ℕ) : binary64ScaleExponent word =
    if binary64ExponentField word = 0 then 1 else binary64ExponentField word := by
  simp only [binary64ScaleExponent, cond_eq_ite, Nat.beq_eq]

/-- The grid magnitude written with `if`, products and quotients: zero for exponent field
`2047`, the significand times `2 ^ (shift - 1075)` when `1075 ≤ shift`, and the significand
divided by `2 ^ (1075 - shift)` otherwise, where `shift` is `binary64GridShift precision word`. -/
theorem decodeWordToGridMagnitude_eq (precision word : ℕ) :
    decodeWordToGridMagnitude precision word =
      if binary64ExponentField word = 2047 then 0
      else if 1075 ≤ binary64GridShift precision word then
        binary64Significand word * 2 ^ (binary64GridShift precision word - 1075)
      else binary64Significand word / 2 ^ (1075 - binary64GridShift precision word) := by
  simp only [decodeWordToGridMagnitude, cond_eq_ite, Nat.beq_eq, Nat.ble_eq, Nat.shiftLeft_eq',
    Nat.shiftLeft_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]

/-- The grid numerator written with `if`: the grid magnitude for sign bit zero, and its
negation otherwise. -/
theorem decodeWordToGrid_eq (precision word : ℕ) : decodeWordToGrid precision word =
    if binary64SignBit word = 0 then (decodeWordToGridMagnitude precision word : ℤ)
    else -(decodeWordToGridMagnitude precision word : ℤ) := by
  simp only [decodeWordToGrid, cond_eq_ite, Nat.beq_eq]

/-- The signed value written with `binary64SignBit`: the magnitude for sign bit zero, and its
negation otherwise. -/
theorem binary64DyadicValue_eq_ite (word : ℕ) : binary64DyadicValue word =
    if binary64SignBit word = 0 then binary64DyadicMagnitude word
    else -binary64DyadicMagnitude word := by
  rw [binary64DyadicValue, binary64SignBit_eq]

/-- Shifting `m * 2 ^ s / 2 ^ E` onto the integers rounds toward zero. -/
theorem shift_round_sound (m s E : ℕ) :
    (((if E ≤ s then m * 2 ^ (s - E) else m / 2 ^ (E - s) : ℕ)) : ℚ) ≤
        (m : ℚ) * 2 ^ s / 2 ^ E ∧
      (m : ℚ) * 2 ^ s / 2 ^ E <
        ((if E ≤ s then m * 2 ^ (s - E) else m / 2 ^ (E - s) : ℕ) : ℚ) + 1 := by
  split_ifs with h
  · have hval : (m : ℚ) * 2 ^ s / 2 ^ E = ((m * 2 ^ (s - E) : ℕ) : ℚ) := by
      push_cast
      rw [pow_sub₀ _ two_ne_zero h, ← div_eq_mul_inv, mul_div_assoc]
    rw [hval]
    exact ⟨le_rfl, lt_add_one _⟩
  · have hval : (m : ℚ) * 2 ^ s / 2 ^ E = (m : ℚ) / ((2 ^ (E - s) : ℕ) : ℚ) := by
      push_cast
      rw [pow_sub₀ _ two_ne_zero (by omega), ← div_eq_mul_inv, div_div_eq_mul_div]
    rw [hval, le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    have := Nat.lt_div_mul_add (a := m) (Nat.two_pow_pos (E - s))
    exact ⟨by exact_mod_cast Nat.div_mul_le_self m (2 ^ (E - s)),
      by exact_mod_cast (by linarith : m < (m / 2 ^ (E - s) + 1) * 2 ^ (E - s))⟩

/-- The shift is exact when it is a left shift or drops only zero bits. -/
theorem shift_round_exact {m s E : ℕ} (h : E ≤ s ∨ m % 2 ^ (E - s) = 0) :
    (((if E ≤ s then m * 2 ^ (s - E) else m / 2 ^ (E - s) : ℕ)) : ℚ) =
      (m : ℚ) * 2 ^ s / 2 ^ E := by
  split_ifs with hs
  · push_cast
    rw [pow_sub₀ _ two_ne_zero hs, ← div_eq_mul_inv, mul_div_assoc]
  · rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero (h.resolve_left hs)) (by positivity)]
    push_cast
    rw [pow_sub₀ _ two_ne_zero (by omega), ← div_eq_mul_inv, div_div_eq_mul_div]

/-- A finite word encodes its significand times `2 ^ (e - 1075)` for its scale exponent `e`. -/
theorem binary64DyadicMagnitude_eq {word : ℕ} (hfin : binary64ExponentField word ≠ 2047) :
    binary64DyadicMagnitude word =
      (binary64Significand word : ℚ) * 2 ^ binary64ScaleExponent word / 2 ^ 1075 := by
  rw [binary64Significand_eq, binary64ScaleExponent_eq]
  rw [binary64ExponentField_eq] at hfin ⊢
  unfold binary64DyadicMagnitude
  dsimp only
  generalize word / 2 ^ 52 % 2048 = e at hfin ⊢
  split_ifs with he hbig
  · rw [show (2 : ℚ) ^ 1075 = 2 ^ 1074 * 2 from pow_succ 2 1074, pow_one,
      mul_div_mul_right _ _ two_ne_zero]
  · rw [pow_sub₀ _ two_ne_zero hbig, ← div_eq_mul_inv, mul_div_assoc]
  · rw [pow_sub₀ _ two_ne_zero (by omega), ← div_eq_mul_inv, div_div_eq_mul_div]

private theorem binary64DyadicMagnitude_eq_zero {word : ℕ}
    (hfin : binary64ExponentField word = 2047) : binary64DyadicMagnitude word = 0 := by
  rw [binary64ExponentField_eq] at hfin
  unfold binary64DyadicMagnitude
  dsimp only
  rw [hfin, ite_eq_right (by norm_num), ite_eq_left rfl]

/-- The scaled magnitude written with the grid shift. -/
private theorem scaled_magnitude_eq {precision word : ℕ}
    (hfin : binary64ExponentField word ≠ 2047) :
    2 ^ precision * binary64DyadicMagnitude word =
      (binary64Significand word : ℚ) * 2 ^ binary64GridShift precision word / 2 ^ 1075 := by
  rw [binary64DyadicMagnitude_eq hfin]
  change _ = (binary64Significand word : ℚ) * 2 ^ (precision + binary64ScaleExponent word) / _
  rw [pow_add]
  generalize (2 : ℚ) ^ 1075 = T
  ring

/-- The grid magnitude is the scaled magnitude rounded toward zero. -/
theorem decodeWordToGridMagnitude_sound (precision word : ℕ) :
    (decodeWordToGridMagnitude precision word : ℚ) ≤
        2 ^ precision * binary64DyadicMagnitude word ∧
      2 ^ precision * binary64DyadicMagnitude word <
        decodeWordToGridMagnitude precision word + 1 := by
  rw [decodeWordToGridMagnitude_eq]
  by_cases hfin : binary64ExponentField word = 2047
  · rw [ite_eq_left hfin, binary64DyadicMagnitude_eq_zero hfin]
    norm_num
  · rw [ite_eq_right hfin, scaled_magnitude_eq hfin]
    exact shift_round_sound _ _ _

/-- The grid numerator of a word lies within one grid unit of its scaled value. -/
theorem decodeWordToGrid_sound (precision word : ℕ) :
    |(decodeWordToGrid precision word : ℝ) - 2 ^ precision * binary64DyadicValue word| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := decodeWordToGridMagnitude_sound precision word
  have hq : |(decodeWordToGrid precision word : ℚ) -
      2 ^ precision * binary64DyadicValue word| ≤ 1 := by
    rw [binary64DyadicValue_eq_ite, decodeWordToGrid_eq, abs_le]
    split_ifs <;> push_cast <;> constructor <;> linarith
  exact_mod_cast hq

/-- When the word's value lies on the grid, the decoding is exact. -/
theorem decodeWordToGrid_exact {precision word : ℕ}
    (h : binary64GridExact precision word = true) :
    (decodeWordToGrid precision word : ℚ) = 2 ^ precision * binary64DyadicValue word := by
  have hmag : (decodeWordToGridMagnitude precision word : ℚ) =
      2 ^ precision * binary64DyadicMagnitude word := by
    rw [decodeWordToGridMagnitude_eq]
    by_cases hfin : binary64ExponentField word = 2047
    · rw [ite_eq_left hfin, binary64DyadicMagnitude_eq_zero hfin]
      norm_num
    · rw [ite_eq_right hfin, scaled_magnitude_eq hfin]
      refine shift_round_exact ?_
      simpa [binary64GridExact, hfin, slotMask_eq, ← Nat.and_two_pow_sub_one_eq_mod] using h
  rw [binary64DyadicValue_eq_ite, decodeWordToGrid_eq]
  split_ifs <;> push_cast [hmag] <;> ring

/-- An exactly decoded word is the grid value of its numerator. -/
theorem binary64DyadicValue_eq_toRat {precision word : ℕ}
    (h : binary64GridExact precision word = true) :
    binary64DyadicValue word =
      FloatLib.Numerics.Interval.BinaryGrid.toRat precision (decodeWordToGrid precision word) := by
  rw [FloatLib.Numerics.Interval.BinaryGrid.toRat, Rat.divInt_eq_div,
    FloatLib.Numerics.Interval.BinaryGrid.scale_eq_pow]
  push_cast
  rw [decodeWordToGrid_exact h]
  field_simp

/-- The biased slot value of the grid numerator of a word, in a slot of width `w`. -/
def biasedGridWord (w precision word : ℕ) : ℕ :=
  cond (Nat.beq (binary64SignBit word) 0)
    (Nat.add (slotBias w) (decodeWordToGridMagnitude precision word))
    (Nat.sub (slotBias w) (decodeWordToGridMagnitude precision word))

/-- Slot `k` of `x` stores the exact grid numerator of `word`: the word encodes a finite
value on the grid, the magnitude is at most the bias, and the slot holds the biased numerator.
Only natural-number operations are used. -/
def gridSlotCheck (w precision : ℕ) (x k word : ℕ) : Bool :=
  !Nat.beq (binary64ExponentField word) 2047 &&
    binary64GridExact precision word &&
    Nat.ble (decodeWordToGridMagnitude precision word) (slotBias w) &&
    Nat.beq (slot w k x) (biasedGridWord w precision word)

/-- A passing slot check identifies the stored entry with the word's grid numerator. -/
theorem signedSlot_eq_decodeWordToGrid {w precision x k word : ℕ}
    (h : gridSlotCheck w precision x k word = true) :
    signedSlot w k x = decodeWordToGrid precision word := by
  simp only [gridSlotCheck, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨_, hle⟩, heq⟩ := h
  rw [signedSlot, heq, decodeWordToGrid_eq, biasedGridWord]
  simp only [cond_eq_ite, Nat.beq_eq, Nat.add_eq, Nat.sub_eq]
  split_ifs <;> omega

/-- A passing slot check gives the word's exact value as the grid value of the stored entry. -/
theorem binary64DyadicValue_eq_toRat_of_gridSlotCheck {w precision x k word : ℕ}
    (h : gridSlotCheck w precision x k word = true) :
    binary64DyadicValue word =
      FloatLib.Numerics.Interval.BinaryGrid.toRat precision (signedSlot w k x) := by
  rw [signedSlot_eq_decodeWordToGrid h]
  simp only [gridSlotCheck, Bool.and_eq_true] at h
  exact binary64DyadicValue_eq_toRat h.1.1.2

/-- Each of the first `n` words of the row `words` of 64-bit slots is stored exactly, as its
grid numerator with `precision` fractional bits, in the slot of the same index and width `w` of
`x`: `gridSlotCheck` for every slot, in a `Nat.rec` loop. -/
def gridRowCheck (w precision x words n : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ Bool) true
    (fun k acc ↦ acc && gridSlotCheck w precision x k (slot 64 k words)) n

/-- A passing row check gives the slot check of every word of the row. -/
theorem gridSlotCheck_of_gridRowCheck {w precision x words n k : ℕ}
    (h : gridRowCheck w precision x words n = true) (hk : k < n) :
    gridSlotCheck w precision x k (slot 64 k words) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h1 hk
    · exact h2

/-- A passing row check gives every word of the row as the grid value of its stored entry. -/
theorem binary64DyadicValue_slot_eq_toRat_of_gridRowCheck {w precision x words n k : ℕ}
    (h : gridRowCheck w precision x words n = true) (hk : k < n) :
    binary64DyadicValue (slot 64 k words) =
      FloatLib.Numerics.Interval.BinaryGrid.toRat precision (signedSlot w k x) :=
  binary64DyadicValue_eq_toRat_of_gridSlotCheck (gridSlotCheck_of_gridRowCheck h hk)

/-! ### Grid values -/

open FloatLib.Numerics.Interval in
/-- The grid value of a numerator is the numerator divided by `2 ^ precision`. -/
theorem binaryGrid_toRat_eq_div (precision : ℕ) (z : ℤ) :
    BinaryGrid.toRat precision z = (z : ℚ) / 2 ^ precision := by
  rw [BinaryGrid.toRat, Rat.divInt_eq_div, BinaryGrid.scale_eq_pow]
  push_cast
  rfl

/-! ### Rows of truncated numerators -/

/-- Slot `k` of `x` stores the grid numerator of `word` rounded toward zero: the word encodes a
finite value, the magnitude is at most the bias, and the slot holds the biased numerator. The
value need not lie on the grid. -/
def gridSlotTruncCheck (w precision : ℕ) (x k word : ℕ) : Bool :=
  !Nat.beq (binary64ExponentField word) 2047 &&
    Nat.ble (decodeWordToGridMagnitude precision word) (slotBias w) &&
    Nat.beq (slot w k x) (biasedGridWord w precision word)

/-- A passing truncated check identifies the stored entry with the word's grid numerator. -/
theorem signedSlot_eq_decodeWordToGrid_of_truncCheck {w precision x k word : ℕ}
    (h : gridSlotTruncCheck w precision x k word = true) :
    signedSlot w k x = decodeWordToGrid precision word := by
  simp only [gridSlotTruncCheck, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨_, hle⟩, heq⟩ := h
  rw [signedSlot, heq, decodeWordToGrid_eq, biasedGridWord]
  simp only [cond_eq_ite, Nat.beq_eq, Nat.add_eq, Nat.sub_eq]
  split_ifs <;> omega

/-- A passing truncated check puts the word's value within one grid step of the stored entry. -/
theorem abs_binary64DyadicValue_sub_signedSlot_le {w precision x k word : ℕ}
    (h : gridSlotTruncCheck w precision x k word = true) :
    |(binary64DyadicValue word : ℝ) - (signedSlot w k x : ℝ) / 2 ^ precision| ≤
      1 / 2 ^ precision := by
  have h1 := decodeWordToGrid_sound precision word
  rw [← signedSlot_eq_decodeWordToGrid_of_truncCheck h] at h1
  have hp : (0 : ℝ) < 2 ^ precision := by positivity
  rw [show (binary64DyadicValue word : ℝ) - (signedSlot w k x : ℝ) / 2 ^ precision =
      -((signedSlot w k x : ℝ) - 2 ^ precision * binary64DyadicValue word) / 2 ^ precision by
    field_simp; ring, abs_div, abs_neg, abs_of_pos hp]
  exact div_le_div_of_nonneg_right h1 hp.le

/-- Each of the first `n` words of the row `words` of 64-bit slots is stored as its grid
numerator rounded toward zero in the slot of the same index and width `w` of `x`. -/
def gridRowTruncCheck (w precision x words n : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ Bool) true
    (fun k acc ↦ acc && gridSlotTruncCheck w precision x k (slot 64 k words)) n

/-- A passing truncated row check gives the slot check of every word of the row. -/
theorem gridSlotTruncCheck_of_gridRowTruncCheck {w precision x words n k : ℕ}
    (h : gridRowTruncCheck w precision x words n = true) (hk : k < n) :
    gridSlotTruncCheck w precision x k (slot 64 k words) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h1 hk
    · exact h2

end CAS.Numerics
