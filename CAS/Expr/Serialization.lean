/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Serialization of checked expressions for kernel read-back

The encoders write checked data into one natural number, so that a single kernel evaluation
computes all of it, and the decoders read the number back in compiled code. The data are a
normal form with its side-condition list, two expression lists, or a list of rational numbers.
No proof depends on this code: a decoded result is certified separately by the kernel, and a
decoding failure only makes the tactic fail.

## Main definitions

* `encodeResult`, `decodeResult`: a normal form together with its side-condition list.
* `encodeLists`, `decodeLists`: two expression lists, such as a requirement collection.
* `encodeRationals`, `decodeRationals`: rational numbers, read back as numerator and
  denominator pairs.

## Implementation notes

The exact tactics evaluate a normalizer run with the kernel's evaluator and read the resulting
normal form and side-condition list back into `Verified.Expr` values before certifying the run
with `decide +kernel`. Reading a constructor tree back node by node costs one kernel evaluation
per node, and every evaluation starts with an empty cache, so a side list with a few dozen nodes
re-evaluates the whole pipeline a few dozen times.

We therefore serialize the whole result into one natural number. The encoder uses only
`Nat.mul`, `Nat.add`, `Nat.pow`, `Nat.div`, `Nat.mod` and comparison, which the kernel computes
natively on literals, so a single kernel evaluation of `encodeResult` produces a literal from
which `decodeResult` recovers the data. The stream is written in postorder into an accumulator,
with the last token in the least significant digit; the decoder therefore reads a node tag first
and its children in reverse order.
-/

@[expose] public section

namespace CAS.Verified.Expr.Serial

/-- Radix of the token stream; every constructor tag and word count is one digit. -/
def radix : Nat := 64

/-- Radix of the words in which arbitrary naturals are written. -/
def wordRadix : Nat := 2 ^ 32

/-- Fuel of the word count in `pushNat`. A word count is one base-`radix` digit, so `pushNat`
writes naturals of at most `63` words; a natural of `64` or more words (from `2 ^ 2016` on)
poisons the stream, and decoding fails. -/
def maxWords : Nat := 64

/-- Number of base-`wordRadix` words of `k`, at least one, computed with structural fuel. -/
def wordCount : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, k => if k < wordRadix then 1 else wordCount fuel (k / wordRadix) + 1

/-- Append a constructor tag. -/
def pushTag (acc tag : Nat) : Nat :=
  acc * radix + tag

/-- Append a natural number: its words, then the word count, one base-`radix` digit. A natural
of `radix` or more words (from `2 ^ 2016` on) has no such count: it poisons the stream (it becomes
`0`), as `pushLongNat` does, and `decodeResult` and `decodeLists` then reject it. -/
def pushNat (acc k : Nat) : Nat :=
  let words := wordCount maxWords k
  if words < radix then pushTag (acc * wordRadix ^ words + k) words else 0

/-- Append an integer: its absolute value, then a sign tag. -/
def pushInt (acc : Nat) (z : Int) : Nat :=
  pushTag (pushNat acc z.natAbs) (if z < 0 then 1 else 0)

/-- Append an expression in postorder, writing variables through `index`. -/
def pushExpr {ι : Type*} (index : ι → Nat) : Nat → Verified.Expr ι → Nat
  | acc, .nat n => pushTag (pushNat acc n) 0
  | acc, .int z => pushTag (pushInt acc z) 1
  | acc, .rat num den => pushTag (pushNat (pushInt acc num) den) 2
  | acc, .pi => pushTag acc 3
  | acc, .e => pushTag acc 4
  | acc, .var i => pushTag (pushNat acc (index i)) 5
  | acc, .add a b => pushTag (pushExpr index (pushExpr index acc a) b) 6
  | acc, .mul a b => pushTag (pushExpr index (pushExpr index acc a) b) 7
  | acc, .sub a b => pushTag (pushExpr index (pushExpr index acc a) b) 8
  | acc, .div a b => pushTag (pushExpr index (pushExpr index acc a) b) 9
  | acc, .neg a => pushTag (pushExpr index acc a) 10
  | acc, .pow a n => pushTag (pushNat (pushExpr index acc a) n) 11
  | acc, .sin a => pushTag (pushExpr index acc a) 12
  | acc, .cos a => pushTag (pushExpr index acc a) 13
  | acc, .atan a => pushTag (pushExpr index acc a) 14
  | acc, .asin a => pushTag (pushExpr index acc a) 15
  | acc, .acos a => pushTag (pushExpr index acc a) 16
  | acc, .exp a => pushTag (pushExpr index acc a) 17
  | acc, .log a => pushTag (pushExpr index acc a) 18
  | acc, .sqrt a => pushTag (pushExpr index acc a) 19
  | acc, .rpow a b => pushTag (pushExpr index (pushExpr index acc a) b) 20

/-- Append a list of expressions in postorder. -/
def pushList {ι : Type*} (index : ι → Nat) : Nat → List (Verified.Expr ι) → Nat
  | acc, [] => pushTag acc 30
  | acc, x :: xs => pushTag (pushList index (pushExpr index acc x) xs) 31

/-- Serialize a normal form together with its side-condition list. The accumulator starts at
`1` so that a leading zero tag is preserved. -/
def encodeResult {ι : Type*} (index : ι → Nat) (expr : Verified.Expr ι)
    (side : List (Verified.Expr ι)) : Nat :=
  pushList index (pushExpr index 1 expr) side

/-- Read a natural number written by `pushNat`. -/
def popNat (n : Nat) : Nat × Nat :=
  let words := n % radix
  let n := n / radix
  (n % wordRadix ^ words, n / wordRadix ^ words)

/-- Read an integer written by `pushInt`. -/
def popInt (n : Nat) : Int × Nat :=
  let sign := n % radix
  let n := n / radix
  let (k, n) := popNat n
  (if sign = 1 then -(k : Int) else (k : Int), n)

/-- Decode one expression written by `pushExpr`, with structural fuel bounding the depth. -/
def decodeExpr : Nat → Nat → Option (Verified.Expr Nat × Nat)
  | 0, _ => none
  | fuel + 1, n =>
      let tag := n % radix
      let n := n / radix
      let binary (mk : Verified.Expr Nat → Verified.Expr Nat → Verified.Expr Nat) :
          Option (Verified.Expr Nat × Nat) := do
        let (b, n) ← decodeExpr fuel n
        let (a, n) ← decodeExpr fuel n
        return (mk a b, n)
      let unary (mk : Verified.Expr Nat → Verified.Expr Nat) :
          Option (Verified.Expr Nat × Nat) := do
        let (a, n) ← decodeExpr fuel n
        return (mk a, n)
      match tag with
      | 0 => let (k, n) := popNat n; some (.nat k, n)
      | 1 => let (z, n) := popInt n; some (.int z, n)
      | 2 =>
          let (den, n) := popNat n
          let (num, n) := popInt n
          some (.rat num den, n)
      | 3 => some (.pi, n)
      | 4 => some (.e, n)
      | 5 => let (i, n) := popNat n; some (.var i, n)
      | 6 => binary .add
      | 7 => binary .mul
      | 8 => binary .sub
      | 9 => binary .div
      | 10 => unary .neg
      | 11 => do
          let (k, n) := popNat n
          let (a, n) ← decodeExpr fuel n
          return (.pow a k, n)
      | 12 => unary .sin
      | 13 => unary .cos
      | 14 => unary .atan
      | 15 => unary .asin
      | 16 => unary .acos
      | 17 => unary .exp
      | 18 => unary .log
      | 19 => unary .sqrt
      | 20 => binary .rpow
      | _ => none

/-- Decode a list written by `pushList`. -/
def decodeList : Nat → Nat → Option (List (Verified.Expr Nat) × Nat)
  | 0, _ => none
  | fuel + 1, n =>
      let tag := n % radix
      let n := n / radix
      match tag with
      | 30 => some ([], n)
      | 31 => do
          let (rest, n) ← decodeList fuel n
          let (x, n) ← decodeExpr fuel n
          return (x :: rest, n)
      | _ => none

/-- Decode a serialized normal form and side list; `none` if the stream is malformed. Every
node consumes at least one digit, so the bit length of the code bounds the recursion depth. -/
def decodeResult (code : Nat) : Option (Verified.Expr Nat × List (Verified.Expr Nat)) := do
  let fuel := code.log2 + 2
  let (side, n) ← decodeList fuel code
  let (expr, n) ← decodeExpr fuel n
  guard (n = 1)
  return (expr, side)

/-- Serialize two expression lists into one natural number, for reading back a requirement
collection (`nonzero` and `positive` lists) in one kernel evaluation. -/
def encodeLists {ι : Type*} (index : ι → Nat) (first second : List (Verified.Expr ι)) : Nat :=
  pushList index (pushList index 1 first) second

/-- Decode two lists written by `encodeLists`; `none` if the stream is malformed. -/
def decodeLists (code : Nat) : Option (List (Verified.Expr Nat) × List (Verified.Expr Nat)) := do
  let fuel := code.log2 + 2
  let (second, n) ← decodeList fuel code
  let (first, n) ← decodeList fuel n
  guard (n = 1)
  return (first, second)

/-! ## Rational fields

A checked numerical query reads a few rational fields (endpoints, a midpoint and a radius) of
one computed value. Reducing the numerator and the denominator of each field separately repeats
the evaluation of that value once per number, since every kernel evaluation starts with an empty
cache. `encodeRationals` writes all of them into one natural number, so that one kernel
evaluation shares the work, and `decodeRationals` reads them back in compiled code. The
numerators and denominators of such fields have thousands of bits, so their word counts are
written with `pushNat` instead of a single base-64 digit (which `pushNat` itself uses, and which
cannot hold a count of 64 words or more). -/

/-- The fuel of the word count in `encodeRationals`. `wordCount maxLongWords` counts up to
`maxLongWords + 1` base-`wordRadix` words, so every number below `2 ^ 131104` is written, far
beyond the precision of any default CEGA query. -/
def maxLongWords : Nat := 4096

/-- Append a natural number below `wordRadix ^ (maxLongWords + 1)`: its words, then their count
written by `pushNat`. A larger number poisons the stream (it becomes `0`), which
`decodeRationals` then rejects. -/
def pushLongNat (acc k : Nat) : Nat :=
  let words := wordCount maxLongWords k
  if k < wordRadix ^ words then pushNat (acc * wordRadix ^ words + k) words else 0

/-- Append a rational number: a sign tag, the magnitude of the numerator, the denominator. -/
def pushRat (acc : Nat) (q : ℚ) : Nat :=
  match q.num with
  | .ofNat n => pushLongNat (pushLongNat (pushTag acc 0) n) q.den
  | .negSucc n => pushLongNat (pushLongNat (pushTag acc 1) (n + 1)) q.den

/-- Serialize rational numbers into one natural number, in order. The accumulator starts at `1`,
which `decodeRationals` checks at the end. -/
def encodeRationals (values : List ℚ) : Nat :=
  values.foldl pushRat 1

/-- Read a natural number written by `pushLongNat`; `none` for a word count above
`maxLongWords + 1`, which no encoder writes. -/
def popLongNat (n : Nat) : Option (Nat × Nat) :=
  let (words, n) := popNat n
  if words > maxLongWords + 1 then none
  else some (n % wordRadix ^ words, n / wordRadix ^ words)

/-- Decode `count` rationals written by `encodeRationals` as numerator and denominator pairs, in
their original order; `none` if the stream is malformed or poisoned. -/
def decodeRationals (count code : Nat) : Option (List (Int × Nat)) := Id.run do
  let mut n := code
  let mut values : List (Int × Nat) := []
  for _ in [0:count] do
    let some (den, rest) := popLongNat n | return none
    let some (magnitude, rest) := popLongNat rest | return none
    let sign := rest % radix
    n := rest / radix
    if sign > 1 then return none
    values := ((if sign = 1 then -(magnitude : Int) else magnitude), den) :: values
  return if n = 1 then some values else none

end CAS.Verified.Expr.Serial
