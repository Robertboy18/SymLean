/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Serialization
meta import CAS.Expr.Serialization

/-!
# The kernel read-back codec at its size limit

The exact tactics read a normal form back from one natural number written by
`Verified.Expr.Serial.encodeResult`. `pushNat` writes the word count of a natural as one base-64
digit, so a natural of 64 or more 32-bit words (from `2 ^ 2016` on) cannot be written: it poisons
the stream and `decodeResult` returns `none`, instead of reading the count modulo 64. A natural
just below the limit is still read back exactly.
-/

set_option linter.hashCommand false

open CAS.Verified.Expr

-- `2 ^ 2000` has 63 words and round-trips.
#guard Serial.decodeResult
    (Serial.encodeResult (ι := Nat) id (.nat (2 ^ 2000)) [.int (-(2 ^ 2000))]) ==
  some (.nat (2 ^ 2000), [.int (-(2 ^ 2000))])

-- `2 ^ 2100` has 66 words and is refused, in the expression and in the side list.
#guard (Serial.decodeResult (Serial.encodeResult (ι := Nat) id (.nat (2 ^ 2100)) [])).isNone
#guard (Serial.decodeResult (Serial.encodeResult (ι := Nat) id (.nat 1) [.nat (2 ^ 2100)])).isNone

-- The exact limit: `2 ^ 2016 - 1` has 63 words and round-trips, `2 ^ 2016` has 64 and is refused.
#guard Serial.decodeResult
    (Serial.encodeResult (ι := Nat) id (.nat (2 ^ 2016 - 1)) [.int (-(2 ^ 2016 - 1))]) ==
  some (.nat (2 ^ 2016 - 1), [.int (-(2 ^ 2016 - 1))])
#guard (Serial.decodeResult (Serial.encodeResult (ι := Nat) id (.nat (2 ^ 2016)) [])).isNone
#guard (Serial.decodeResult (Serial.encodeResult (ι := Nat) id (.nat 1) [.int (2 ^ 2016)])).isNone

-- `decodeLists` reads back `encodeLists` up to the same limit, in either list.
#guard Serial.decodeLists (Serial.encodeLists (ι := Nat) id [.nat (2 ^ 2016 - 1)] [.nat 2]) ==
  some ([.nat (2 ^ 2016 - 1)], [.nat 2])
#guard (Serial.decodeLists (Serial.encodeLists (ι := Nat) id [.nat (2 ^ 2016)] [.nat 2])).isNone
#guard (Serial.decodeLists (Serial.encodeLists (ι := Nat) id [.nat 1] [.nat (2 ^ 2016)])).isNone

-- `encodeRationals` writes word counts with `pushNat`, so its numerators and denominators may
-- have up to `maxLongWords + 1 = 4097` words: everything below `2 ^ 131104` is read back, and
-- `2 ^ 131104`, as a numerator or a denominator, poisons the stream.
#guard Serial.decodeRationals 2
    (Serial.encodeRationals [((2 ^ 131104 - 1 : ℕ) : ℚ), -1 / ((2 ^ 131104 - 1 : ℕ) : ℚ)]) ==
  some [(((2 ^ 131104 - 1 : ℕ) : ℤ), 1), (-1, 2 ^ 131104 - 1)]
#guard (Serial.decodeRationals 1 (Serial.encodeRationals [((2 ^ 131104 : ℕ) : ℚ)])).isNone
#guard (Serial.decodeRationals 2
    (Serial.encodeRationals [1, 1 / ((2 ^ 131104 : ℕ) : ℚ)])).isNone
