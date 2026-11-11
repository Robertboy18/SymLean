/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import CAS.Numerics.Binary64

/-!
# Binary64 arithmetic on natural-number words

A binary64 value is determined by its 64-bit word: the sign is bit 63 (`signField`), the biased
exponent occupies bits 52 to 62 (`binary64ExponentField`) and the fraction bits 0 to 51
(`fractionField`); `pack` assembles a word from its fields. `add` and `mul` compute FloatLib's
nearest-even binary64 addition and multiplication on words with natural-number operations only,
and for finite operands they return the words of `Model.Spec.add` and `Model.Spec.mul`
(`spec_add`, `spec_mul`). Multiplying or dividing a normal value by a power of two is exact when
the result is normal (`mul_pow_two`, `spec_div_pow_two`).

The kernel evaluates `Nat.log2` by recursion, so certificates with many roundings use the
branch-free sum of two normal significands of one sign, `sumExponent` and `sumSignificand`: the
exact sum is aligned at the smaller exponent, its leading bit is located from the gap and one
carry bit, and `roundHalfEven` rounds by adding half a unit less one and the parity of the
quotient before truncating (`add_pack_fast`, for exponent gaps up to 110 and no overflow).

## Implementation notes

We do not prove the rounding from scratch. `add` and `mul` restate on words the algorithms of
FloatLib's unsigned-scale kernels `FiniteScaleAdd.roundSum` and `FiniteProductRound.round`
(`roundSum_eq`, `roundScaled_eq`), and `spec_add` and `spec_mul` combine these with FloatLib's
proofs that the kernels round the exact dyadic sum and product
(`Model.FiniteKernel.Internal.addComponents_eq`, `Model.FiniteKernel.mul_eq_spec`). The
definitions call `Nat.add`, `Nat.shiftRight`, `Nat.land`, `Nat.beq` and `cond` directly, so
kernel reduction evaluates a word operation with the natural-number literal extensions and
without unfolding type classes or bit vectors.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The kernels
  `FiniteScaleAdd.roundSum` and `FiniteProductRound.round` and their proofs.
* IEEE Computer Society, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, IEEE,
  Piscataway, NJ, 2019, <https://doi.org/10.1109/IEEESTD.2019.8766229>. The binary64 format and
  rounding to nearest, ties to even.
* Lean 4, release v4.35.0, <https://github.com/leanprover/lean4>. `type_checker::reduce_nat` in
  `src/kernel/type_checker.cpp` lists the operations the kernel evaluates on literals;
  `Nat.log2` is not among them.
-/

@[expose] public section

namespace CAS.Numerics.Binary64Word

open FloatLib.Floats.Formats.BinaryInterchange

/-! ### Fields of a word -/

/-- Bit `i` of `m`, by one shift and one mask. -/
def bit (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

/-- The sign bit, bit 63 of a binary64 word. -/
def signField (w : ℕ) : Bool := bit w 63

/-- The fraction field, bits 0 to 51 of a binary64 word. -/
def fractionField (w : ℕ) : ℕ := Nat.land w 4503599627370495

/-- The integer significand of a finite word, with the implicit leading bit of a normal value. -/
def significand (w : ℕ) : ℕ :=
  bif Nat.beq (binary64ExponentField w) 0 then fractionField w
  else Nat.add 4503599627370496 (fractionField w)

/-- The word with sign `s`, the low 11 bits of `e` as exponent field and the low 52 bits of `f` as
fraction field. -/
def pack (s : Bool) (e f : ℕ) : ℕ :=
  Nat.lor (Nat.lor (bif s then 9223372036854775808 else 0)
    (Nat.shiftLeft (Nat.land e 2047) 52)) (Nat.land f 4503599627370495)

/-- The word of the zero with sign `s`. -/
def signedZero (s : Bool) : ℕ := bif s then 9223372036854775808 else 0

/-- The word of the infinity with sign `s`. -/
def signedInfinity (s : Bool) : ℕ := bif s then 18442240474082181120 else 9218868437227405312

/-! ### Rounding -/

/-- `m / 2 ^ s` rounded to the nearest natural number, ties to even: the quotient is increased
when the guard bit is set and a lower bit is set or the quotient is odd. -/
def roundShiftEven (m s : ℕ) : ℕ :=
  bif Nat.beq s 0 then m
  else bif bit m (Nat.sub s 1) &&
      (!Nat.beq (Nat.land m (Nat.sub (Nat.shiftLeft 1 (Nat.sub s 1)) 1)) 0 || bit m s) then
    Nat.add (Nat.shiftRight m s) 1
  else Nat.shiftRight m s

/-- The subnormal branch of `roundScaled`, from the rounded fraction. -/
def roundSubnormal (s : Bool) (fraction : ℕ) : ℕ :=
  bif Nat.beq fraction 0 then signedZero s
  else bif Nat.beq fraction 4503599627370496 then pack s 1 0
  else pack s 0 fraction

/-- The normal branch of `roundScaled`, from the leading position and the rounded significand. -/
def roundNormal (s : Bool) (position rounded : ℕ) : ℕ :=
  bif Nat.beq rounded 9007199254740992 then
    bif Nat.blt 3171 (Nat.add position 1) then signedInfinity s
    else pack s (Nat.sub (Nat.add position 1) 1125) 0
  else
    bif Nat.blt 3171 position then signedInfinity s
    else pack s (Nat.sub position 1125) (Nat.sub rounded 4503599627370496)

/-- The word of the binary64 rounding of `(-1) ^ s * p * 2 ^ (sc - 2148)`: FloatLib's
`FiniteProductRound.round` on binary64. -/
def roundScaled (s : Bool) (p sc : ℕ) : ℕ :=
  bif Nat.beq p 0 then signedZero s
  else bif Nat.blt (Nat.add (Nat.log2 p) sc) 1126 then
    roundSubnormal s (bif Nat.blt sc 1074 then roundShiftEven p (Nat.sub 1074 sc)
      else Nat.shiftLeft p (Nat.sub sc 1074))
  else
    roundNormal s (Nat.add (Nat.log2 p) sc)
      (bif Nat.ble 52 (Nat.log2 p) then roundShiftEven p (Nat.sub (Nat.log2 p) 52)
        else Nat.shiftLeft p (Nat.sub 52 (Nat.log2 p)))

/-! ### Addition and multiplication -/

/-- Rounding of a signed magnitude at an addition scale. -/
def roundMagnitude (s : Bool) (m sc : ℕ) : ℕ := roundScaled s m (Nat.add sc 1074)

/-- Rounding of the exact sum of two signed magnitudes at one scale. -/
def roundMagnitudes (ls rs : Bool) (l r sc : ℕ) : ℕ :=
  bif ls == rs then roundMagnitude ls (Nat.add l r) sc
  else bif Nat.beq l r then signedZero (ls && rs)
  else bif Nat.blt l r then roundMagnitude rs (Nat.sub r l) sc
  else roundMagnitude ls (Nat.sub l r) sc

/-- The magnitude kept by `roundAligned` for a large scale gap, with a sticky low bit. -/
def stickyMagnitude (hs ls : Bool) (high low gap : ℕ) : ℕ :=
  bif hs == ls then
    bif Nat.beq low (Nat.shiftLeft (Nat.shiftRight low (Nat.sub gap 55)) (Nat.sub gap 55)) then
      Nat.add (Nat.shiftLeft high 55) (Nat.shiftRight low (Nat.sub gap 55))
    else Nat.lor (Nat.add (Nat.shiftLeft high 55) (Nat.shiftRight low (Nat.sub gap 55))) 1
  else
    bif Nat.beq low (Nat.shiftLeft (Nat.shiftRight low (Nat.sub gap 55)) (Nat.sub gap 55)) then
      Nat.sub (Nat.shiftLeft high 55) (Nat.shiftRight low (Nat.sub gap 55))
    else
      Nat.lor (Nat.sub (Nat.sub (Nat.shiftLeft high 55) (Nat.shiftRight low (Nat.sub gap 55))) 1) 1

/-- Rounding of the sum of a magnitude at a higher scale and one at the base scale. -/
def roundAligned (hs ls : Bool) (high low gap sc : ℕ) : ℕ :=
  bif Nat.blt 110 gap && Nat.blt (Nat.add (Nat.log2 low) 1) gap && !Nat.beq high 0 then
    roundMagnitude hs (stickyMagnitude hs ls high low gap) (Nat.add sc (Nat.sub gap 55))
  else roundMagnitudes hs ls (Nat.shiftLeft high gap) low sc

/-- The word of the rounded sum of two signed significands at their scales: FloatLib's
`FiniteScaleAdd.roundSum` on binary64 at the addition offset. -/
def roundSum (ls rs : Bool) (lm lsc rm rsc : ℕ) : ℕ :=
  bif Nat.beq lm 0 then
    bif Nat.beq rm 0 then signedZero (ls && rs) else roundMagnitude rs rm rsc
  else bif Nat.beq rm 0 then roundMagnitude ls lm lsc
  else bif Nat.ble lsc rsc then roundAligned rs ls rm lm (Nat.sub rsc lsc) lsc
  else roundAligned ls rs lm rm (Nat.sub lsc rsc) rsc

/-- The word of the nearest-even binary64 sum of two finite words. -/
def add (x y : ℕ) : ℕ :=
  roundSum (signField x) (signField y) (significand x) (Nat.sub (binary64ExponentField x) 1)
    (significand y) (Nat.sub (binary64ExponentField y) 1)

/-- The word of the nearest-even binary64 product of two finite words. -/
def mul (x y : ℕ) : ℕ :=
  bif Nat.beq (significand x) 0 || Nat.beq (significand y) 0 then
    signedZero (Bool.xor (signField x) (signField y))
  else roundScaled (Bool.xor (signField x) (signField y))
    (Nat.mul (significand x) (significand y))
    (Nat.add (Nat.sub (binary64ExponentField x) 1) (Nat.sub (binary64ExponentField y) 1))

/-! ### Sums of one sign without leading-bit search -/

/-- The exact sum of the significand `mh` shifted by `g` and the significand `ml`. -/
def alignedSum (g mh ml : ℕ) : ℕ := Nat.add (Nat.shiftLeft mh g) ml

/-- The rounding shift of `alignedSum g mh ml` for normal significands: `g`, or `g + 1` when the
sum carries into bit `53 + g`. -/
def alignedShift (g mh ml : ℕ) : ℕ :=
  bif Nat.blt (alignedSum g mh ml) (Nat.shiftLeft 1 (Nat.add 53 g)) then g else Nat.add g 1

/-- Exponent field and significand of the nearest-even sum of the normal significands `mh` at
exponent field `el + g` and `ml` at exponent field `el`, of one sign. -/
def alignedFields (g mh el ml : ℕ) : ℕ × ℕ :=
  bif Nat.beq (roundShiftEven (alignedSum g mh ml) (alignedShift g mh ml)) 9007199254740992 then
    (Nat.add (Nat.add el (alignedShift g mh ml)) 1, 4503599627370496)
  else
    (Nat.add el (alignedShift g mh ml), roundShiftEven (alignedSum g mh ml) (alignedShift g mh ml))

/-- `alignedFields` with the operand of larger exponent field first. -/
def sumFields (e1 m1 e2 m2 : ℕ) : ℕ × ℕ :=
  bif Nat.ble e1 e2 then alignedFields (Nat.sub e2 e1) m2 e1 m1
  else alignedFields (Nat.sub e1 e2) m1 e2 m2

/-- `x / 2 ^ s` rounded to nearest, ties to even, for `1 ≤ s`, without branches: half the unit
minus one and the parity of the quotient are added before truncating. -/
def roundHalfEven (x s : ℕ) : ℕ :=
  Nat.shiftRight (Nat.add (Nat.add x (Nat.sub (Nat.shiftLeft 1 (Nat.sub s 1)) 1))
    (Nat.land (Nat.shiftRight x s) 1)) s

/-- The distance of two exponent fields. -/
def sumGap (e1 e2 : ℕ) : ℕ := Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)

/-- The exact sum of two significands at the smaller of their exponent fields. -/
def sumExact (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))

/-- The rounding shift of `sumExact` for normal significands: the gap, plus one when the sum
carries. -/
def sumShift (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.add (sumGap e1 e2) (Nat.shiftRight (sumExact e1 m1 e2 m2) (Nat.add 53 (sumGap e1 e2)))

/-- The rounded significand of `sumExact`, before a carry into the next binade. -/
def sumRounded (e1 m1 e2 m2 : ℕ) : ℕ := roundHalfEven (sumExact e1 m1 e2 m2) (sumShift e1 m1 e2 m2)

/-- The exponent field of the nearest-even sum of two normal significands of one sign. -/
def sumExponent (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.sub e1 (Nat.sub e1 e2)) (sumShift e1 m1 e2 m2))
    (Nat.shiftRight (sumRounded e1 m1 e2 m2) 53)

/-- The significand of the nearest-even sum of two normal significands of one sign. -/
def sumSignificand (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.shiftRight (sumRounded e1 m1 e2 m2) (Nat.shiftRight (sumRounded e1 m1 e2 m2) 53)

/-- `sumExponent` with its auxiliary definitions unfolded, for kernel evaluation. -/
def sumExponentInline (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.sub e1 (Nat.sub e1 e2)) (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))
    (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1)))
    (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)))))) (Nat.shiftRight (Nat.shiftRight
    (Nat.add (Nat.add (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2
    e1))) (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))
    (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1)))
    (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))))) 1)) 1)) (Nat.land (Nat.shiftRight
    (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add
    (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub
    e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2
    e1)))))) 1)) (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add
    (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add
    (Nat.sub e1 e2) (Nat.sub e2 e1)))))) 53)

/-- `sumSignificand` with its auxiliary definitions unfolded, for kernel evaluation. -/
def sumSignificandInline (e1 m1 e2 m2 : ℕ) : ℕ :=
  Nat.shiftRight (Nat.shiftRight (Nat.add (Nat.add (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2))
    (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.add (Nat.add
    (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2))
    (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)))))
    1)) 1)) (Nat.land (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2
    (Nat.sub e2 e1))) (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add
    (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add
    (Nat.sub e1 e2) (Nat.sub e2 e1)))))) 1)) (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))
    (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1)))
    (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)))))) (Nat.shiftRight (Nat.shiftRight
    (Nat.add (Nat.add (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2
    e1))) (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))
    (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1)))
    (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1))))) 1)) 1)) (Nat.land (Nat.shiftRight
    (Nat.add (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add
    (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add (Nat.shiftLeft m1 (Nat.sub
    e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add (Nat.sub e1 e2) (Nat.sub e2
    e1)))))) 1)) (Nat.add (Nat.add (Nat.sub e1 e2) (Nat.sub e2 e1)) (Nat.shiftRight (Nat.add
    (Nat.shiftLeft m1 (Nat.sub e1 e2)) (Nat.shiftLeft m2 (Nat.sub e2 e1))) (Nat.add 53 (Nat.add
    (Nat.sub e1 e2) (Nat.sub e2 e1)))))) 53)

/-! ### Words of FloatLib values -/

local notation "B64" => FloatFormat.binary64

/-- `Nat.beq x y` is the Boolean `decide (x = y)`. Kept because core states only the proposition
`Nat.beq x y = true` (`Nat.beq_eq`), not this Bool-level `= decide` form, which the `cond` rewrites
in this file use. -/
theorem beq_eq_decide (x y : ℕ) : Nat.beq x y = decide (x = y) :=
  Bool.eq_iff_iff.mpr (by simp)

/-- `Nat.blt x y` is the Boolean `decide (x < y)`. Kept because core states only the proposition
`Nat.blt x y = true` (`Nat.blt_eq`), not this Bool-level `= decide` form. -/
theorem blt_eq_decide (x y : ℕ) : Nat.blt x y = decide (x < y) :=
  Bool.eq_iff_iff.mpr (by simp)

/-- `Nat.ble x y` is the Boolean `decide (x ≤ y)`. Kept because core states only the proposition
`Nat.ble x y = true` (`Nat.ble_eq`), not this Bool-level `= decide` form. -/
theorem ble_eq_decide (x y : ℕ) : Nat.ble x y = decide (x ≤ y) :=
  Bool.eq_iff_iff.mpr (by simp)

/-- For `x ≠ y`, `Nat.beq x y = false`. Kept because core has only the converse
`Nat.ne_of_beq_eq_false` and the form `beq_false_of_ne` for `==`, not this Bool-level form for
`Nat.beq`. -/
theorem beq_eq_false_of_ne {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  simpa [beq_eq_decide] using h

/-- `bit m i` is `m.testBit i`. -/
theorem bit_eq (m i : ℕ) : bit m i = m.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold bit
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    beq_eq_decide]

/-- Bit `i` of the sign mask `2 ^ 63`, written `9223372036854775808`, is set exactly when
`i = 63`. -/
theorem testBit_signMask (i : ℕ) : (9223372036854775808 : ℕ).testBit i = decide (63 = i) := by
  rw [show (9223372036854775808 : ℕ) = 2 ^ 63 by norm_num]
  exact Nat.testBit_two_pow

/-- `pack s e f` written with `|||`, `<<<` and remainders: the bitwise or of the sign mask
`2 ^ 63` (or `0` when `s` is false), `(e % 2 ^ 11) <<< 52` and `f % 2 ^ 52`. -/
theorem pack_eq_lor (s : Bool) (e f : ℕ) :
    pack s e f = ((bif s then 2 ^ 63 else 0) ||| ((e % 2 ^ 11) <<< 52)) ||| f % 2 ^ 52 := by
  unfold pack
  simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.land_eq]
  rw [show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num,
    show (4503599627370495 : ℕ) = 2 ^ 52 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- The exponent field of `pack s e f` is `e % 2048`. -/
theorem binary64ExponentField_pack (s : Bool) (e f : ℕ) :
    binary64ExponentField (pack s e f) = e % 2048 := by
  rw [pack_eq_lor]
  unfold binary64ExponentField
  simp only [Nat.land_eq, Nat.shiftRight_eq']
  rw [show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num, show (2048 : ℕ) = 2 ^ 11 by norm_num]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 11
  · cases s <;> simp [hi, show ¬63 = 52 + i by omega, testBit_signMask]
  · cases s <;> simp [hi, testBit_signMask]

/-- The fraction field of `pack s e f` is `f % 2 ^ 52`. -/
theorem fractionField_pack (s : Bool) (e f : ℕ) : fractionField (pack s e f) = f % 2 ^ 52 := by
  rw [pack_eq_lor]
  unfold fractionField
  simp only [Nat.land_eq]
  rw [show (4503599627370495 : ℕ) = 2 ^ 52 - 1 by norm_num]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 52
  · cases s <;> simp [hi, show ¬63 = i by omega, show ¬52 ≤ i by omega, testBit_signMask]
  · cases s <;> simp [hi, testBit_signMask]

/-- The sign bit of `pack s e f` is `s`. -/
theorem signField_pack (s : Bool) (e f : ℕ) : signField (pack s e f) = s := by
  rw [pack_eq_lor]
  unfold signField
  rw [bit_eq]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
  cases s <;> simp [testBit_signMask]

/-- The binary64 value `Model.ofNatBits w` has bit pattern `w % 2 ^ 64`. -/
theorem toNatBits_ofNatBits (w : ℕ) :
    (Model.ofNatBits (fmt := B64) w).toNatBits = w % 2 ^ 64 :=
  BitVec.toNat_ofNat w 64

/-- FloatLib's sign bit of the binary64 value `Model.ofNatBits w` is `signField w`. -/
theorem signBit_ofNatBits (w : ℕ) :
    Model.signBit (Model.ofNatBits (fmt := B64) w) = signField w := by
  rw [Model.signBit_eq_internal_apply]
  unfold Model.Internal.signBit signField
  rw [toNatBits_ofNatBits, bit_eq]
  change (w % 2 ^ 64).testBit 63 = _
  rw [Nat.testBit_mod_two_pow]
  simp

/-- FloatLib's exponent field of the binary64 value `Model.ofNatBits w` is
`binary64ExponentField w`. -/
theorem expField_ofNatBits (w : ℕ) :
    Model.expField (Model.ofNatBits (fmt := B64) w) = binary64ExponentField w := by
  rw [Model.expField_eq_internal_apply]
  unfold Model.Internal.expField binary64ExponentField
  rw [toNatBits_ofNatBits, show FloatFormat.binary64.fracWidth = 52 from rfl,
    show FloatFormat.expAllOnesNat FloatFormat.binary64 = 2 ^ 11 - 1 from rfl, Nat.land_eq,
    Nat.shiftRight_eq', show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 11
  · simp [hi, show 52 + i < 64 by omega]
  · simp [hi]

/-- FloatLib's fraction field of the binary64 value `Model.ofNatBits w` is `fractionField w`. -/
theorem fracField_ofNatBits (w : ℕ) :
    Model.fracField (Model.ofNatBits (fmt := B64) w) = fractionField w := by
  rw [Model.fracField_eq_internal_apply]
  unfold Model.Internal.fracField fractionField
  rw [toNatBits_ofNatBits,
    show FloatFormat.fracMaskNat FloatFormat.binary64 = 2 ^ 52 - 1 from rfl, Nat.land_eq,
    show (4503599627370495 : ℕ) = 2 ^ 52 - 1 by norm_num]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 52
  · simp [hi, show i < 64 by omega]
  · simp [hi]

/-- The binary64 value `Model.ofNatBits w` is finite exactly when the exponent field of `w` is not
`2047`. -/
theorem isFinite_ofNatBits (w : ℕ) :
    Model.isFinite (Model.ofNatBits (fmt := B64) w) = true ↔ binary64ExponentField w ≠ 2047 := by
  change Model.IEEE.isFinite _ = true ↔ _
  unfold Model.IEEE.isFinite
  rw [expField_ofNatBits]
  change (binary64ExponentField w != 2047) = true ↔ _
  simp

/-- For a word `w` whose exponent field is not `2047`, FloatLib's `FiniteKernel.decode?` of
`Model.ofNatBits w` returns the components `signField w`, `binary64ExponentField w` and
`significand w`. -/
theorem decode_ofNatBits (w : ℕ) (hw : binary64ExponentField w ≠ 2047) :
    Model.FiniteKernel.decode? (Model.ofNatBits (fmt := B64) w) =
      some ⟨signField w, binary64ExponentField w, significand w⟩ := by
  have hfinite := (isFinite_ofNatBits w).mpr hw
  unfold Model.FiniteKernel.decode?
  simp only [hfinite, Bool.not_true, Bool.false_eq_true, ite_false, expField_ofNatBits,
    fracField_ofNatBits, signBit_ofNatBits, Option.some.injEq,
    Model.FiniteKernel.Components.mk.injEq,
    true_and]
  unfold Model.FiniteKernel.decodeMantissa significand
  by_cases he : binary64ExponentField w = 0
  · simp [he]
  · simp [he, Model.pow2_eq_two_pow, show FloatFormat.binary64.fracWidth = 52 from rfl]

/-- For a word `w` whose exponent field is not `2047`, `Model.toDyadic?` of `Model.ofNatBits w` is
the dyadic value of the components `signField w`, `binary64ExponentField w` and `significand w`. -/
theorem toDyadic_ofNatBits (w : ℕ) (hw : binary64ExponentField w ≠ 2047) :
    Model.toDyadic? (Model.ofNatBits (fmt := B64) w) =
      some ((⟨signField w, binary64ExponentField w, significand w⟩ :
        Model.FiniteKernel.Components).toDyadic B64) := by
  rw [Model.FiniteKernel.toDyadic_eq_decode, decode_ofNatBits w hw]
  rfl

/-- FloatLib's `Model.ofFields` on binary64 with sign `s`, exponent `e` and fraction `f` is
`Model.ofNatBits (pack s e f)`. -/
theorem ofFields_eq (s : Bool) (e f : ℕ) :
    Model.ofFields B64 s e f = Model.ofNatBits (pack s e f) := by
  rw [Model.ofFields_eq_internal]
  unfold Model.Internal.ofFields Model.Internal.mkBits
  rw [BitVec.ofNatLT_eq_ofNat]
  unfold pack
  cases s <;> rfl

/-- Binary64 positive zero is `Model.ofNatBits 0`. -/
theorem posZero_eq : Model.posZero B64 = Model.ofNatBits 0 := rfl

/-- Binary64 negative zero is `Model.ofNatBits (2 ^ 63)`, with `2 ^ 63` written as a literal. -/
theorem negZero_eq : Model.negZero B64 = Model.ofNatBits 9223372036854775808 := rfl

/-- The binary64 zero with sign `s` is `Model.ofNatBits (signedZero s)`. -/
theorem zero_eq (s : Bool) : Model.zero B64 s = Model.ofNatBits (signedZero s) := by
  cases s <;> rfl

/-- Binary64 positive infinity is `Model.ofNatBits` of the word with exponent field `2047`, fraction
zero and sign bit clear. -/
theorem posInf_eq : Model.posInf B64 = Model.ofNatBits 9218868437227405312 := rfl

/-- Binary64 negative infinity is `Model.ofNatBits` of the word with exponent field `2047`, fraction
zero and sign bit set. -/
theorem negInf_eq : Model.negInf B64 = Model.ofNatBits 18442240474082181120 := by decide

/-- `roundShiftEven m s` equals FloatLib's `roundShiftRightEven m s` for all `m` and `s`. -/
theorem roundShiftEven_eq (m s : ℕ) :
    roundShiftEven m s = FloatLib.Numerics.roundShiftRightEven m s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [roundShiftEven]
  · rw [FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky m s hs]
    unfold roundShiftEven
    simp only [beq_eq_decide, hs.ne', decide_false, Bool.cond_false, bit_eq, Nat.sub_eq,
      Nat.land_eq,
      Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.add_eq,
      Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, ← decide_not]
    cases (m.testBit (s - 1) && (decide (m % 2 ^ (s - 1) ≠ 0) || m.testBit s)) <;> rfl

/-! ### Rounding and addition agree with FloatLib's kernels -/

/-- FloatLib's `FiniteProductRound.round` on binary64 is `Model.ofNatBits (roundScaled s p sc)`, for
all `s`, `p` and `sc`. -/
theorem roundScaled_eq (s : Bool) (p sc : ℕ) :
    Model.FiniteProductRound.round B64 s p sc = Model.ofNatBits (roundScaled s p sc) := by
  unfold Model.FiniteProductRound.round roundScaled roundSubnormal roundNormal signedZero
    signedInfinity
  simp only [show FloatFormat.binary64.bias = 1023 from rfl,
    show FloatFormat.binary64.fracWidth = 52 from rfl,
    show FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 = 1074 from rfl,
    Model.pow2_eq_two_pow, roundShiftEven_eq, ofFields_eq, negZero_eq, posZero_eq, negInf_eq,
    posInf_eq, beq_eq_decide, blt_eq_decide, ble_eq_decide, Bool.cond_eq_ite, decide_eq_true_eq,
    beq_iff_eq, Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', apply_ite (Model.ofNatBits (fmt := B64)),
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
  split_ifs <;> rfl

/-- FloatLib's `FiniteScaleAdd.roundMagnitude` on binary64 at offset `1074` is
`Model.ofNatBits (roundMagnitude s m sc)`, for all `s`, `m` and `sc`. -/
theorem roundMagnitude_eq (s : Bool) (m sc : ℕ) :
    Model.FiniteScaleAdd.roundMagnitude B64 1074 s m sc = Model.ofNatBits (roundMagnitude s m sc) :=
  roundScaled_eq s m (sc + 1074)

/-- FloatLib's `FiniteScaleAdd.roundMagnitudes` on binary64 at offset `1074` is
`Model.ofNatBits (roundMagnitudes ls rs l r sc)`, for all arguments. -/
theorem roundMagnitudes_eq (ls rs : Bool) (l r sc : ℕ) :
    Model.FiniteScaleAdd.roundMagnitudes B64 1074 ls rs l r sc =
      Model.ofNatBits (roundMagnitudes ls rs l r sc) := by
  unfold Model.FiniteScaleAdd.roundMagnitudes roundMagnitudes
  simp only [beq_eq_decide, blt_eq_decide, Bool.cond_eq_ite, decide_eq_true_eq, beq_iff_eq,
    Nat.add_eq, Nat.sub_eq, apply_ite (Model.ofNatBits (fmt := B64)), ← roundMagnitude_eq, zero_eq]

/-- FloatLib's `FiniteScaleAdd.roundAligned` on binary64 at offset `1074` is
`Model.ofNatBits (roundAligned hs ls high low gap sc)`, for all arguments. -/
theorem roundAligned_eq (hs ls : Bool) (high low gap sc : ℕ) :
    Model.FiniteScaleAdd.roundAligned B64 1074 hs ls high low gap sc =
      Model.ofNatBits (roundAligned hs ls high low gap sc) := by
  unfold Model.FiniteScaleAdd.roundAligned roundAligned stickyMagnitude
  simp only [show FloatFormat.binary64.fracWidth = 52 from rfl, beq_eq_decide, blt_eq_decide,
    Bool.cond_eq_ite, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, beq_iff_eq, Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq',
    Nat.shiftRight_eq', Nat.lor_eq, Nat.reduceMul, Nat.reduceAdd, and_assoc]
  split_ifs <;> simp only [roundMagnitude_eq, roundMagnitudes_eq]

/-- FloatLib's `FiniteScaleAdd.roundSum` on binary64 at offset `1074` is
`Model.ofNatBits (roundSum ls rs lm lsc rm rsc)`, for all arguments. -/
theorem roundSum_eq (ls rs : Bool) (lm lsc rm rsc : ℕ) :
    Model.FiniteScaleAdd.roundSum B64 1074 ls rs lm lsc rm rsc =
      Model.ofNatBits (roundSum ls rs lm lsc rm rsc) := by
  unfold Model.FiniteScaleAdd.roundSum roundSum
  simp only [beq_eq_decide, ble_eq_decide, Bool.cond_eq_ite, decide_eq_true_eq, beq_iff_eq,
    Nat.sub_eq, apply_ite (Model.ofNatBits (fmt := B64)), ← roundMagnitude_eq, ← roundAligned_eq,
    zero_eq]

/-- FloatLib's finite scale `FiniteKernel.scale e` of an exponent field is `e - 1`, truncated
subtraction, so zero for `e = 0`. -/
theorem scale_eq (e : ℕ) : Model.FiniteKernel.scale e = e - 1 := by
  unfold Model.FiniteKernel.scale
  split <;> simp_all

/-- Binary64 addition of finite words is `add`. -/
theorem spec_add (x y : ℕ) (hx : binary64ExponentField x ≠ 2047)
    (hy : binary64ExponentField y ≠ 2047) :
    Model.Spec.add (Model.ofNatBits (fmt := B64) x) (Model.ofNatBits y) =
      Model.ofNatBits (add x y) := by
  unfold Model.Spec.add
  rw [toDyadic_ofNatBits x hx, toDyadic_ofNatBits y hy]
  dsimp only
  rw [Model.roundDyadic_eq_internal]
  change Model.FiniteKernel.addComponents B64 _ _ = _
  rw [← Model.FiniteKernel.Internal.addComponents_eq]
  unfold Model.FiniteKernel.Internal.addComponents
  rw [ite_eq_left FloatFormat.isIEEE_binary64,
    show Model.FiniteKernel.finiteScaleOffset B64 = 1074 from rfl, roundSum_eq]
  simp only [scale_eq, add, Nat.sub_eq]

/-- Binary64 multiplication of finite words is `mul`. -/
theorem spec_mul (x y : ℕ) (hx : binary64ExponentField x ≠ 2047)
    (hy : binary64ExponentField y ≠ 2047) :
    Model.Spec.mul (Model.ofNatBits (fmt := B64) x) (Model.ofNatBits y) =
      Model.ofNatBits (mul x y) := by
  have h := Model.FiniteKernel.mul_eq_spec (Model.ofNatBits (fmt := B64) x) (Model.ofNatBits y)
  rw [← Model.FiniteKernel.mulRuntime_eq] at h
  unfold Model.Spec.mul
  rw [toDyadic_ofNatBits x hx, toDyadic_ofNatBits y hy] at h ⊢
  dsimp only at h ⊢
  apply Option.some_injective
  rw [apply_ite Option.some, ← h]
  unfold Model.FiniteKernel.mulRuntime?
  rw [Model.FiniteKernel.withFinite_eq, decode_ofNatBits x hx, Option.bind_some,
    Model.FiniteKernel.withFinite_eq, decode_ofNatBits y hy, Option.bind_some]
  unfold Model.FiniteKernel.mulFields mul
  simp only [FloatFormat.isIEEE_binary64, ite_true, roundScaled_eq, zero_eq, scale_eq,
    beq_eq_decide,
    ← Bool.decide_or, Bool.cond_eq_ite, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Nat.mul_eq,
    Nat.add_eq, Nat.sub_eq, apply_ite (Model.ofNatBits (fmt := B64))]

/-! ### Division by a power of two -/

/-- The fraction field of every word is less than `2 ^ 52`. -/
theorem fractionField_lt (w : ℕ) : fractionField w < 2 ^ 52 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- For a word with nonzero exponent field, the significand is `2 ^ 52` plus the fraction field. -/
theorem significand_of_normal {w : ℕ} (hw : binary64ExponentField w ≠ 0) :
    significand w = 2 ^ 52 + fractionField w := by
  simp [significand, hw]

/-- For `2 ^ 52 ≤ m < 2 ^ 53`, FloatLib's `RationalBinary.floorLog2 m (2 ^ 52)` is `0`. -/
theorem floorLog2_normal {m : ℕ} (h1 : 2 ^ 52 ≤ m) (h2 : m < 2 ^ 53) :
    FloatLib.Numerics.RationalBinary.floorLog2 m (2 ^ 52) = 0 := by
  have hm : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).2 ⟨h1, h2⟩
  unfold FloatLib.Numerics.RationalBinary.floorLog2
  rw [hm, Nat.log2_two_pow]
  have hlt : FloatLib.Numerics.RationalBinary.lessThanPowerOfTwo m (2 ^ 52) 0 = false := by
    change decide (m < Nat.shiftLeft (2 ^ 52) 0) = false
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_zero, decide_eq_false_iff_not, not_lt]
    exact h1
  have hge : FloatLib.Numerics.RationalBinary.atLeastPowerOfTwo m (2 ^ 52) 1 = false := by
    change decide (m ≥ Nat.shiftLeft (2 ^ 52) 1) = false
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, decide_eq_false_iff_not, not_le]
    omega
  simp only [Int.ofNat_eq_natCast, sub_self, hlt, Bool.false_eq_true, ite_false, zero_add, hge]

/-- FloatLib's `RationalBinary.scaleByPowerOfTwo m d 52` is `(m <<< 52, d)`. -/
theorem scaleByPowerOfTwo_fiftyTwo (m d : ℕ) :
    FloatLib.Numerics.RationalBinary.scaleByPowerOfTwo m d 52 = (m <<< 52, d) := rfl

/-- FloatLib's `roundQuotientEven (m <<< 52) (2 ^ 52)` is `m`, with `2 ^ 52` written as a
literal. -/
theorem roundQuotientEven_shift (m : ℕ) :
    FloatLib.Numerics.roundQuotientEven (m <<< 52) 4503599627370496 = m := by
  unfold FloatLib.Numerics.roundQuotientEven
  simp [Nat.shiftLeft_eq]

/-- Dividing a normal binary64 word by a positive power of two is exact when the quotient is
normal: the exponent field decreases and the fraction is kept. -/
theorem spec_div_pow_two (x y : ℕ) (hx : 1 ≤ binary64ExponentField x)
    (hx' : binary64ExponentField x ≠ 2047) (hy : 1 ≤ binary64ExponentField y)
    (hy' : binary64ExponentField y ≠ 2047) (hys : signField y = false)
    (hyf : fractionField y = 0) (hlo : binary64ExponentField y + 1 ≤ binary64ExponentField x + 1023)
    (hhi : binary64ExponentField x + 1023 ≤ binary64ExponentField y + 2046) :
    Model.Spec.div (Model.ofNatBits (fmt := B64) x) (Model.ofNatBits y) =
      Model.ofNatBits
        (pack (signField x) (binary64ExponentField x + 1023 - binary64ExponentField y)
          (fractionField x)) := by
  have hmx := significand_of_normal (w := x) (by omega)
  have hmy := significand_of_normal (w := y) (by omega)
  rw [hyf, Nat.add_zero] at hmy
  have hf := fractionField_lt x
  unfold Model.Spec.div
  rw [toDyadic_ofNatBits x hx', toDyadic_ofNatBits y hy']
  dsimp only
  simp only [Model.FiniteKernel.Components.toDyadic, Model.FiniteKernel.dyadicExponent, hmx, hmy,
    hys,
    beq_iff_eq, show binary64ExponentField x ≠ 0 by omega,
    show binary64ExponentField y ≠ 0 by omega,
    Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, not_false_eq_true, ite_false,
    Nat.add_eq_zero_iff, Bool.xor_false]
  unfold Model.roundRatScaled
  rw [dite_eq_left FloatFormat.isIEEE_binary64]
  unfold Model.ieeeRoundRatScaled
  rw [floorLog2_normal (by omega) (by omega)]
  simp only [show FloatFormat.binary64.exponentBias = 1023 from rfl,
    show FloatFormat.binary64.fracWidth = 52 from rfl,
    show FloatFormat.binary64.bias = 1023 from rfl,
    show FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 = 1023 from rfl,
    show FloatFormat.ieeeMinNormalExponent FloatFormat.binary64 = -1022 from rfl,
    show FloatFormat.normalMantissaExpOffset FloatFormat.binary64 = 1075 from rfl,
    Int.ofNat_eq_natCast, zero_add, sub_zero, beq_iff_eq, OfNat.ofNat_ne_zero, false_and,
    ite_false, Nat.add_eq_zero_iff, Model.pow2_eq_two_pow, Nat.reducePow, Nat.reduceAdd,
    Nat.cast_ofNat, scaleByPowerOfTwo_fiftyTwo, roundQuotientEven_shift]
  norm_num only at hf
  split_ifs <;> try (exfalso; omega)
  rw [ofFields_eq]
  have he : ((binary64ExponentField x : ℤ) - 1023 - 52 -
      ((binary64ExponentField y : ℤ) - 1023 - 52) + 1023).toNat =
      binary64ExponentField x + 1023 - binary64ExponentField y := by omega
  rw [he, Nat.add_sub_cancel_left]

/-- Dividing a zero word by a finite nonzero word gives the zero with the product of the signs. -/
theorem spec_div_zero (x y : ℕ) (hx : binary64ExponentField x = 0) (hxf : fractionField x = 0)
    (hy : binary64ExponentField y ≠ 2047) (hy0 : significand y ≠ 0) :
    Model.Spec.div (Model.ofNatBits (fmt := B64) x) (Model.ofNatBits y) =
      Model.ofNatBits (signedZero (Bool.xor (signField x) (signField y))) := by
  have hmx : significand x = 0 := by simp [significand, hx, hxf]
  unfold Model.Spec.div
  rw [toDyadic_ofNatBits x (by omega), toDyadic_ofNatBits y hy]
  dsimp only
  simp only [Model.FiniteKernel.Components.toDyadic, hmx, hy0, beq_iff_eq, ite_true, ite_false,
    zero_eq]

/-! ### Sums and products without leading-bit search -/

/-- `alignedSum g mh ml` is `mh * 2 ^ g + ml`. -/
theorem alignedSum_eq (g mh ml : ℕ) : alignedSum g mh ml = mh * 2 ^ g + ml := by
  simp [alignedSum, Nat.shiftLeft_eq]

/-- `alignedShift g mh ml` is `g` when `mh * 2 ^ g + ml < 2 ^ (53 + g)`, and `g + 1` otherwise. -/
theorem alignedShift_eq (g mh ml : ℕ) :
    alignedShift g mh ml = if mh * 2 ^ g + ml < 2 ^ (53 + g) then g else g + 1 := by
  simp only [alignedShift, alignedSum_eq, blt_eq_decide, Nat.shiftLeft_eq', Nat.one_shiftLeft,
    Nat.add_eq, Bool.cond_decide]

/-- For `2 ^ 52 ≤ mh < 2 ^ 53` and `ml < 2 ^ 53`, `Nat.log2 (alignedSum g mh ml)` is
`52 + alignedShift g mh ml`. -/
theorem log2_alignedSum {g mh ml : ℕ} (h1 : 2 ^ 52 ≤ mh) (h2 : mh < 2 ^ 53) (h3 : ml < 2 ^ 53) :
    Nat.log2 (alignedSum g mh ml) = 52 + alignedShift g mh ml := by
  have ht : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  rw [alignedShift_eq, alignedSum_eq, Nat.log2_eq_iff (by positivity)]
  have hlo : 2 ^ 52 * 2 ^ g ≤ mh * 2 ^ g := Nat.mul_le_mul_right _ h1
  have hhi : mh * 2 ^ g < 2 ^ 53 * 2 ^ g := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
  have hml : ml < 2 ^ 53 * 2 ^ g := lt_of_lt_of_le h3 (Nat.le_mul_of_pos_right _ (by positivity))
  split_ifs with hc
  · refine ⟨?_, by rwa [show 52 + g + 1 = 53 + g by omega]⟩
    rw [pow_add]
    omega
  · refine ⟨?_, ?_⟩
    · rw [show 52 + (g + 1) = 53 + g by omega]
      omega
    · rw [show 52 + (g + 1) + 1 = 53 + 1 + g by omega, pow_add, pow_succ]
      omega

/-- For `1 ≤ e < 2048` and `f < 2 ^ 52`, the significand of `pack s e f` is `2 ^ 52 + f`. -/
theorem significand_pack {s : Bool} {e f : ℕ} (he : 1 ≤ e) (he' : e < 2048) (hf : f < 2 ^ 52) :
    significand (pack s e f) = 2 ^ 52 + f := by
  simp only [significand, binary64ExponentField_pack, fractionField_pack, Nat.mod_eq_of_lt he',
    Nat.mod_eq_of_lt hf, beq_eq_decide, show e ≠ 0 by omega, decide_false, Bool.cond_false,
    Nat.add_eq]
  norm_num

/-- For `2 ^ 52 ≤ mh < 2 ^ 53`, `ml < 2 ^ 53`, `1 ≤ el` and an exponent field
`(alignedFields g mh el ml).1 ≤ 2046`, `roundScaled s` of `alignedSum g mh ml` at scale
`el - 1 + 1074` is the word packed with sign `s`, that exponent field and the fraction
`(alignedFields g mh el ml).2 - 2 ^ 52`. -/
theorem roundScaled_aligned {s : Bool} {g mh ml el : ℕ} (h1 : 2 ^ 52 ≤ mh) (h2 : mh < 2 ^ 53)
    (h3 : ml < 2 ^ 53) (hel : 1 ≤ el)
    (hov : (alignedFields g mh el ml).1 ≤ 2046) :
    roundScaled s (alignedSum g mh ml) (el - 1 + 1074) =
      pack s (alignedFields g mh el ml).1 ((alignedFields g mh el ml).2 - 2 ^ 52) := by
  have hlog := log2_alignedSum (g := g) h1 h2 h3
  have hpos : alignedSum g mh ml ≠ 0 := by
    rw [alignedSum_eq]; have : 1 ≤ 2 ^ g := Nat.one_le_two_pow; positivity
  unfold roundScaled roundNormal
  unfold alignedFields at hov ⊢
  simp only [beq_eq_decide, blt_eq_decide, ble_eq_decide, Bool.cond_decide, hpos, ite_false,
    hlog, Nat.add_eq, Nat.sub_eq] at hov ⊢
  simp only [show ¬52 + alignedShift g mh ml + (el - 1 + 1074) < 1126 by omega, ite_false,
    show 52 ≤ 52 + alignedShift g mh ml by omega, ite_true,
    show 52 + alignedShift g mh ml - 52 = alignedShift g mh ml by omega]
  split_ifs at hov ⊢ with hc hov1 hov2
  · omega
  · rw [show 52 + alignedShift g mh ml + (el - 1 + 1074) + 1 - 1125 =
      el + alignedShift g mh ml + 1 by omega, show (4503599627370496 : ℕ) - 2 ^ 52 = 0 by norm_num]
  · omega
  · rw [show 52 + alignedShift g mh ml + (el - 1 + 1074) - 1125 = el + alignedShift g mh ml by
      omega, show (4503599627370496 : ℕ) = 2 ^ 52 by norm_num]

/-- The sum of two normal words of one sign whose exponent fields differ by at most 110 is given
by `sumFields`, without a leading-bit search, when it is normal. -/
theorem add_pack {s : Bool} {e1 f1 e2 f2 : ℕ} (he1 : 1 ≤ e1) (he1' : e1 < 2048) (he2 : 1 ≤ e2)
    (he2' : e2 < 2048) (hf1 : f1 < 2 ^ 52) (hf2 : f2 < 2 ^ 52) (hg1 : e2 - e1 ≤ 110)
    (hg2 : e1 - e2 ≤ 110) (hov : (sumFields e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2)).1 ≤ 2046) :
    add (pack s e1 f1) (pack s e2 f2) =
      pack s (sumFields e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2)).1
        ((sumFields e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2)).2 - 2 ^ 52) := by
  unfold add
  rw [signField_pack, signField_pack, binary64ExponentField_pack, binary64ExponentField_pack,
    significand_pack he1 he1' hf1, significand_pack he2 he2' hf2, Nat.mod_eq_of_lt he1',
    Nat.mod_eq_of_lt he2']
  unfold sumFields at hov ⊢
  unfold roundSum roundAligned roundMagnitudes roundMagnitude
  simp only [beq_eq_decide, blt_eq_decide, ble_eq_decide, Bool.cond_decide, Nat.sub_eq,
    Nat.add_eq, beq_self_eq_true, Bool.cond_true, show 2 ^ 52 + f1 ≠ 0 by positivity,
    show 2 ^ 52 + f2 ≠ 0 by positivity, ite_false] at hov ⊢
  by_cases h : e1 ≤ e2
  · simp only [h, show e1 - 1 ≤ e2 - 1 by omega, show ¬110 < e2 - 1 - (e1 - 1) by omega,
      ite_true] at hov ⊢
    rw [show e2 - 1 - (e1 - 1) = e2 - e1 by omega]
    exact roundScaled_aligned (by omega) (by omega) (by omega) he1 hov
  · simp only [h, show ¬e1 - 1 ≤ e2 - 1 by omega, show ¬110 < e1 - 1 - (e2 - 1) by omega,
      ite_false] at hov ⊢
    rw [show e1 - 1 - (e2 - 1) = e1 - e2 by omega]
    exact roundScaled_aligned (by omega) (by omega) (by omega) he2 hov

/-- `roundShiftEven (2 ^ 52 * m) 52 = m`, with `2 ^ 52` written as a literal. -/
theorem roundShiftEven_mul_two_pow (m : ℕ) : roundShiftEven (4503599627370496 * m) 52 = m := by
  rw [roundShiftEven_eq, FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky _ _ (by norm_num)]
  have h1 : 4503599627370496 * m / 2 ^ 52 = m := by
    rw [show (4503599627370496 : ℕ) = 2 ^ 52 by norm_num,
      Nat.mul_div_cancel_left _ (by positivity)]
  have h2 : (4503599627370496 * m).testBit (52 - 1) = false := by
    rw [Nat.testBit_eq_decide_div_mod_eq,
      show (4503599627370496 : ℕ) * m = 2 ^ (52 - 1) * (2 * m) by norm_num; ring,
      Nat.mul_div_cancel_left _ (by positivity)]
    simp
  rw [h1, h2]
  rfl

/-- Multiplying a normal word by a positive power of two is exact when the product is normal. -/
theorem mul_pow_two {y x : ℕ} (hys : signField y = false) (hyf : fractionField y = 0)
    (hy : 1 ≤ binary64ExponentField y) (hx : 1 ≤ binary64ExponentField x)
    (hlo : 1024 ≤ binary64ExponentField x + binary64ExponentField y)
    (hhi : binary64ExponentField x + binary64ExponentField y ≤ 3069) :
    mul y x =
      pack (signField x) (binary64ExponentField x + binary64ExponentField y - 1023)
        (fractionField x) := by
  have hmy : significand y = 4503599627370496 := by
    simp [significand, show binary64ExponentField y ≠ 0 by omega, hyf]
  have hmx : significand x = 4503599627370496 + fractionField x := by
    simp [significand, show binary64ExponentField x ≠ 0 by omega]
  have hf := fractionField_lt x
  have hP : Nat.log2 (4503599627370496 * (4503599627370496 + fractionField x)) = 104 := by
    rw [Nat.log2_eq_iff (by positivity)]
    constructor
    · rw [show (2 : ℕ) ^ 104 = 4503599627370496 * 4503599627370496 by norm_num]
      exact Nat.mul_le_mul_left _ (by omega)
    · rw [show (2 : ℕ) ^ (104 + 1) = 4503599627370496 * 9007199254740992 by norm_num]
      exact Nat.mul_lt_mul_of_pos_left (by norm_num at hf ⊢; omega) (by positivity)
  unfold mul roundScaled roundNormal
  simp only [hmy, hmx, hys, Bool.false_xor, beq_eq_decide, blt_eq_decide, ble_eq_decide,
    Bool.cond_decide, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, hP, Nat.reduceSub, Nat.reduceLeDiff,
    ite_true, roundShiftEven_mul_two_pow]
  norm_num at hf
  simp only [show (decide ((4503599627370496 : ℕ) = 0) ||
      decide (4503599627370496 + fractionField x = 0)) = false by simp, Bool.cond_false,
    show ¬104 + (binary64ExponentField y - 1 + (binary64ExponentField x - 1)) < 1126 by omega,
    show ¬4503599627370496 + fractionField x = 9007199254740992 by omega,
    show ¬3171 < 104 + (binary64ExponentField y - 1 + (binary64ExponentField x - 1)) by omega,
    show 4503599627370496 * (4503599627370496 + fractionField x) ≠ 0 by positivity, ite_false]
  rw [show 104 + (binary64ExponentField y - 1 + (binary64ExponentField x - 1)) - 1125 =
    binary64ExponentField x + binary64ExponentField y - 1023 by omega, Nat.add_sub_cancel_left]

/-- Binary64 multiplication by a positive power of two of a normal word with normal product. -/
theorem spec_mul_pow_two {y x : ℕ} (hys : signField y = false) (hyf : fractionField y = 0)
    (hy : 1 ≤ binary64ExponentField y) (hy' : binary64ExponentField y ≠ 2047)
    (hx : 1 ≤ binary64ExponentField x) (hx' : binary64ExponentField x ≠ 2047)
    (hlo : 1024 ≤ binary64ExponentField x + binary64ExponentField y)
    (hhi : binary64ExponentField x + binary64ExponentField y ≤ 3069) :
    Model.Spec.mul (Model.ofNatBits (fmt := B64) y) (Model.ofNatBits x) =
      Model.ofNatBits
        (pack (signField x) (binary64ExponentField x + binary64ExponentField y - 1023)
          (fractionField x)) := by
  rw [spec_mul y x hy' hx', mul_pow_two hys hyf hy hx hlo hhi]

/-- For `1 ≤ s`, the branch-free `roundHalfEven x s` equals `roundShiftEven x s`. -/
theorem roundHalfEven_eq {x s : ℕ} (hs : 1 ≤ s) : roundHalfEven x s = roundShiftEven x s := by
  rw [roundShiftEven_eq, FloatLib.Numerics.roundShiftRightEven_eq_roundQuotientEven]
  unfold roundHalfEven FloatLib.Numerics.roundQuotientEven
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.sub_eq,
    Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.land_eq, Nat.and_one_is_mod]
  have hd : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (s - 1) := by positivity
  have hx := Nat.div_add_mod x (2 ^ s)
  have hr := Nat.mod_lt x (show 0 < 2 ^ s by positivity)
  have hp := Nat.mod_lt (x / 2 ^ s) (show 0 < 2 by norm_num)
  generalize x / 2 ^ s = q at hx hp ⊢
  generalize x % 2 ^ s = r at hx hr ⊢
  generalize 2 ^ (s - 1) = h at hd hpos ⊢
  generalize 2 ^ s = d at hd hx hr ⊢
  subst hd
  rw [← hx, show 2 * h * q + r + (h - 1) + q % 2 = (r + (h - 1) + q % 2) + 2 * h * q by ring,
    Nat.add_mul_div_left _ _ (by omega)]
  by_cases h1 : 2 * r < 2 * h
  · rw [Nat.div_eq_of_lt (by omega)]
    simp [h1]
  · by_cases h2 : 2 * h < 2 * r
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      simp [h1, h2]; omega
    · have hrh : r = h := by omega
      subst hrh
      rcases Nat.mod_two_eq_zero_or_one q with hq | hq
      · rw [hq, Nat.div_eq_of_lt (by omega)]
        simp
      · rw [hq, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
        simp; omega

/-- For `mh < 2 ^ 53` and `ml < 2 ^ 53`, `alignedSum g mh ml < 2 ^ (54 + g)`. -/
theorem alignedSum_lt {g mh ml : ℕ} (h2 : mh < 2 ^ 53) (h3 : ml < 2 ^ 53) :
    alignedSum g mh ml < 2 ^ (54 + g) := by
  rw [alignedSum_eq, pow_add, show (2 : ℕ) ^ 54 = 2 * 2 ^ 53 by norm_num]
  have : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have : mh * 2 ^ g < 2 ^ 53 * 2 ^ g := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
  nlinarith

/-- For `mh < 2 ^ 53` and `ml < 2 ^ 53`, `alignedShift g mh ml` is `g` plus the carry bit
`alignedSum g mh ml >>> (53 + g)`. -/
theorem alignedShift_eq_shiftRight {g mh ml : ℕ} (h2 : mh < 2 ^ 53) (h3 : ml < 2 ^ 53) :
    alignedShift g mh ml = g + alignedSum g mh ml >>> (53 + g) := by
  have hlt := alignedSum_lt (g := g) h2 h3
  rw [alignedShift_eq, ← alignedSum_eq, Nat.shiftRight_eq_div_pow]
  split_ifs with hc
  · rw [Nat.div_eq_of_lt hc]; rfl
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by rw [pow_add] at hlt ⊢; omega)]

/-- For `2 ^ (52 + s) ≤ x < 2 ^ (53 + s)`, `2 ^ 52 ≤ roundShiftEven x s ≤ 2 ^ 53`. -/
theorem roundShiftEven_bounds {x s : ℕ} (hlo : 2 ^ (52 + s) ≤ x) (hhi : x < 2 ^ (53 + s)) :
    2 ^ 52 ≤ roundShiftEven x s ∧ roundShiftEven x s ≤ 2 ^ 53 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp only [roundShiftEven, beq_eq_decide, decide_true, Bool.cond_true]
    omega
  · rw [roundShiftEven_eq, FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky _ _ hs]
    have h1 : 2 ^ 52 ≤ x / 2 ^ s := by
      rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add]; exact hlo
    have h2 : x / 2 ^ s < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; exact hhi
    split_ifs <;> omega

/-- For significands `mh` and `ml` in `[2 ^ 52, 2 ^ 53)`, `alignedFields g mh el ml` is computed
with `roundHalfEven` and shifts: with `S = g + alignedSum g mh ml >>> (53 + g)` and
`R = roundHalfEven (alignedSum g mh ml) S`, its exponent field is `el + S + R >>> 53` and its
significand is `R >>> (R >>> 53)`. -/
theorem alignedFields_eq {g mh el ml : ℕ} (h1 : 2 ^ 52 ≤ mh) (h2 : mh < 2 ^ 53) (h3 : 2 ^ 52 ≤ ml)
    (h4 : ml < 2 ^ 53) :
    alignedFields g mh el ml =
      (el + (g + alignedSum g mh ml >>> (53 + g)) +
          roundHalfEven (alignedSum g mh ml) (g + alignedSum g mh ml >>> (53 + g)) >>> 53,
        roundHalfEven (alignedSum g mh ml) (g + alignedSum g mh ml >>> (53 + g)) >>>
          (roundHalfEven (alignedSum g mh ml) (g + alignedSum g mh ml >>> (53 + g)) >>> 53)) := by
  have hS := alignedShift_eq_shiftRight (g := g) h2 h4
  have hlog := log2_alignedSum (g := g) h1 h2 h4
  have hX0 : alignedSum g mh ml ≠ 0 := by rw [alignedSum_eq]; positivity
  have hb := (Nat.log2_eq_iff hX0).1 hlog
  have hS1 : 1 ≤ alignedShift g mh ml := by
    rw [alignedShift_eq]
    split_ifs with hc
    · rcases Nat.eq_zero_or_pos g with rfl | hg
      · simp at hc; omega
      · exact hg
    · omega
  rw [← hS, roundHalfEven_eq hS1]
  have hR := roundShiftEven_bounds hb.1
    ((by omega : 52 + alignedShift g mh ml + 1 = 53 + alignedShift g mh ml) ▸ hb.2)
  unfold alignedFields
  generalize roundShiftEven (alignedSum g mh ml) (alignedShift g mh ml) = R at hR ⊢
  simp only [beq_eq_decide, Bool.cond_decide, Nat.add_eq, Nat.shiftRight_eq_div_pow]
  by_cases hc : R = 9007199254740992
  · subst hc
    rw [ite_eq_left rfl, show (9007199254740992 : ℕ) / 2 ^ 53 = 1 by norm_num,
      show (9007199254740992 : ℕ) / 2 ^ 1 = 4503599627370496 by norm_num]
  · rw [ite_eq_right hc, Nat.div_eq_of_lt (by omega), pow_zero, Nat.div_one, Nat.add_zero]

/-- For significands `m1` and `m2` in `[2 ^ 52, 2 ^ 53)`, `sumFields e1 m1 e2 m2` is
`(sumExponent e1 m1 e2 m2, sumSignificand e1 m1 e2 m2)`. -/
theorem sumFields_eq {e1 m1 e2 m2 : ℕ} (h1 : 2 ^ 52 ≤ m1) (h1' : m1 < 2 ^ 53) (h2 : 2 ^ 52 ≤ m2)
    (h2' : m2 < 2 ^ 53) :
    sumFields e1 m1 e2 m2 = (sumExponent e1 m1 e2 m2, sumSignificand e1 m1 e2 m2) := by
  unfold sumFields sumExponent sumSignificand sumRounded sumShift sumExact sumGap
  simp only [ble_eq_decide, Bool.cond_decide, Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq',
    Nat.shiftRight_eq']
  by_cases h : e1 ≤ e2
  · rw [ite_eq_left h, alignedFields_eq h2 h2' h1 h1']
    have hx : m1 <<< (e1 - e2) + m2 <<< (e2 - e1) = alignedSum (e2 - e1) m2 m1 := by
      rw [alignedSum_eq, show e1 - e2 = 0 by omega]; simp [Nat.shiftLeft_eq]; ring
    rw [hx, show e1 - e2 = 0 by omega, Nat.zero_add, Nat.sub_zero]
  · rw [ite_eq_right h, alignedFields_eq h1 h1' h2 h2']
    have hx : m1 <<< (e1 - e2) + m2 <<< (e2 - e1) = alignedSum (e1 - e2) m1 m2 := by
      rw [alignedSum_eq, show e2 - e1 = 0 by omega]; simp [Nat.shiftLeft_eq]
    rw [hx, show e2 - e1 = 0 by omega, Nat.add_zero, show e1 - (e1 - e2) = e2 by omega]

/-- The sum of two normal words of one sign whose exponent fields differ by at most 110, with the
branch-free fields `sumExponent` and `sumSignificand`, when it is normal. -/
theorem add_pack_fast {s : Bool} {e1 f1 e2 f2 : ℕ} (he1 : 1 ≤ e1) (he1' : e1 < 2048) (he2 : 1 ≤ e2)
    (he2' : e2 < 2048) (hf1 : f1 < 2 ^ 52) (hf2 : f2 < 2 ^ 52) (hg : sumGap e1 e2 ≤ 110)
    (hov : sumExponent e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2) ≤ 2046) :
    add (pack s e1 f1) (pack s e2 f2) =
      pack s (sumExponent e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2))
        (sumSignificand e1 (2 ^ 52 + f1) e2 (2 ^ 52 + f2) - 2 ^ 52) := by
  have h := sumFields_eq (e1 := e1) (e2 := e2) (show 2 ^ 52 ≤ 2 ^ 52 + f1 by omega)
    (show 2 ^ 52 + f1 < 2 ^ 53 by omega) (show 2 ^ 52 ≤ 2 ^ 52 + f2 by omega)
    (show 2 ^ 52 + f2 < 2 ^ 53 by omega)
  simp only [sumGap, Nat.add_eq, Nat.sub_eq] at hg
  rw [add_pack he1 he1' he2 he2' hf1 hf2 (by omega) (by omega) (by rw [h]; exact hov), h]

/-- For significands `mh` and `ml` in `[2 ^ 52, 2 ^ 53)`, the significand
`(alignedFields g mh el ml).2` lies in `[2 ^ 52, 2 ^ 53)`. -/
theorem alignedFields_snd_bounds {g mh el ml : ℕ} (h1 : 2 ^ 52 ≤ mh) (h2 : mh < 2 ^ 53)
    (h3 : 2 ^ 52 ≤ ml) (h4 : ml < 2 ^ 53) :
    2 ^ 52 ≤ (alignedFields g mh el ml).2 ∧ (alignedFields g mh el ml).2 < 2 ^ 53 := by
  have hlog := log2_alignedSum (g := g) h1 h2 h4
  have hX0 : alignedSum g mh ml ≠ 0 := by rw [alignedSum_eq]; positivity
  have hb := (Nat.log2_eq_iff hX0).1 hlog
  have hR := roundShiftEven_bounds hb.1
    ((by omega : 52 + alignedShift g mh ml + 1 = 53 + alignedShift g mh ml) ▸ hb.2)
  unfold alignedFields
  generalize roundShiftEven (alignedSum g mh ml) (alignedShift g mh ml) = R at hR ⊢
  simp only [beq_eq_decide, Bool.cond_decide]
  split_ifs with hc
  · norm_num
  · omega

/-- For significands `m1` and `m2` in `[2 ^ 52, 2 ^ 53)`, `sumSignificand e1 m1 e2 m2` lies in
`[2 ^ 52, 2 ^ 53)`. -/
theorem sumSignificand_bounds {e1 m1 e2 m2 : ℕ} (h1 : 2 ^ 52 ≤ m1) (h1' : m1 < 2 ^ 53)
    (h2 : 2 ^ 52 ≤ m2) (h2' : m2 < 2 ^ 53) :
    2 ^ 52 ≤ sumSignificand e1 m1 e2 m2 ∧ sumSignificand e1 m1 e2 m2 < 2 ^ 53 := by
  have h := congrArg Prod.snd (sumFields_eq (e1 := e1) (e2 := e2) h1 h1' h2 h2')
  simp only at h
  rw [← h]
  unfold sumFields
  simp only [ble_eq_decide, Bool.cond_decide, Nat.sub_eq]
  split_ifs
  · exact alignedFields_snd_bounds h2 h2' h1 h1'
  · exact alignedFields_snd_bounds h1 h1' h2 h2'

/-- `sumExponent e1 m1 e2 m2` is at least `e1 - (e1 - e2)`, the smaller exponent field. -/
theorem le_sumExponent (e1 m1 e2 m2 : ℕ) : e1 - (e1 - e2) ≤ sumExponent e1 m1 e2 m2 := by
  unfold sumExponent
  simp only [Nat.add_eq, Nat.sub_eq]
  omega

/-- `sumExponentInline` is `sumExponent`, by unfolding the definitions. -/
theorem sumExponentInline_eq (e1 m1 e2 m2 : ℕ) :
    sumExponentInline e1 m1 e2 m2 = sumExponent e1 m1 e2 m2 := rfl

/-- `sumSignificandInline` is `sumSignificand`, by unfolding the definitions. -/
theorem sumSignificandInline_eq (e1 m1 e2 m2 : ℕ) :
    sumSignificandInline e1 m1 e2 m2 = sumSignificand e1 m1 e2 m2 := rfl

/-- `Nat.land a (2 ^ 63)`, with `2 ^ 63` written as a literal, is `2 ^ 63` when `signField a` and
`0` otherwise. -/
theorem land_signMask (a : ℕ) :
    Nat.land a 9223372036854775808 = bif signField a then 9223372036854775808 else 0 := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  unfold signField
  rw [bit_eq]
  simp only [Nat.land_eq, Nat.testBit_and, testBit_signMask]
  by_cases hi : 63 = i
  · subst hi; cases a.testBit 63 <;> simp [testBit_signMask]
  · cases a.testBit 63 <;> simp [hi, testBit_signMask]

/-- The word with the sign bit of `a`, exponent field `e` and fraction `f`, for fields in range. -/
theorem lor_eq_pack {a e f : ℕ} (he : e < 2048) (hf : f < 2 ^ 52) :
    Nat.lor (Nat.lor (Nat.land a 9223372036854775808) (Nat.shiftLeft e 52)) f =
      pack (signField a) e f := by
  rw [land_signMask]
  unfold pack
  rw [show Nat.land e 2047 = e by
      rw [Nat.land_eq, show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)],
    show Nat.land f 4503599627370495 = f by
      rw [Nat.land_eq, show (4503599627370495 : ℕ) = 2 ^ 52 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hf]]

/-- If `Nat.land (Nat.xor a b) (2 ^ 63) = 0`, with `2 ^ 63` written as a literal, then `a` and `b`
have the same sign bit. -/
theorem signField_eq_of_xor {a b : ℕ} (h : Nat.land (Nat.xor a b) 9223372036854775808 = 0) :
    signField a = signField b := by
  have h1 := congrArg (Nat.testBit · 63) h
  simp only [Nat.land_eq, Nat.testBit_and, testBit_signMask, Nat.zero_testBit] at h1
  unfold signField
  rw [bit_eq, bit_eq]
  have h2 : (Nat.xor a b).testBit 63 = false := by simpa using h1
  rw [show Nat.xor a b = a ^^^ b from rfl, Nat.testBit_xor] at h2
  cases ha : a.testBit 63 <;> cases hb : b.testBit 63 <;> simp_all

end CAS.Numerics.Binary64Word
