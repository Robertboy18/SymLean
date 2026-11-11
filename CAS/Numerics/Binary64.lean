/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Rat.Defs
public import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.Json
public import CAS.Numerics.Json

/-!
# Exact dyadic decoding of finite binary64 inputs

`binary64DyadicValue word` is the exact rational that a binary64 word encodes: with sign bit
`s`, biased exponent `E` and fraction `f`, it is `(-1) ^ s (2 ^ 52 + f) 2 ^ (E - 1075)` for
`0 < E < 2047` and `(-1) ^ s f / 2 ^ 1074` for subnormals and signed zeros. A source word must
have exponent less than 2047 to represent a finite IEEE 754 value; the remaining encodings,
infinities and NaNs, decode to zero. Hexadecimal input can be embedded as a balanced,
length-indexed word tree using `binary64_words% text`, or as rows of `q` words, one natural
number per row, using `binary64_word_rows% q text`, so that word `l` of row `i` is
`slot 64 l (t.get i)`.

## Main definitions

* `binary64DyadicValue`, `binary64DyadicMagnitude`: the exact signed and unsigned values of a
  word.
* `binary64ExponentField`: the biased exponent, bits 52 to 62, by one shift and one mask.
* `Binary64WordTree`, `Binary64WordTree.ofPackedSlots`: length-indexed balanced trees of words,
  built from the slots of one packed natural number.
* `binary64_words%`, `binary64_word_rows%`: elaborators that import hexadecimal text.

## Implementation notes

Decoding uses integer and rational arithmetic, including subnormals and signed zero, and
evaluates no floating-point operation, so a decoded value is a rational the kernel can compute.
The elaborators pack the words into one natural literal, 64 bits per word, behind an
irreducible auxiliary definition, and `Binary64WordTree.ofPacked`, the tree `ofPackedSlots 64`
of 64-bit slots, is built from it: the left half of each node keeps the low slots and the right
half reads a shifted copy. Looking up one word therefore reduces only its branch of the tree,
and compiled code builds the tree once. In the kernel the lookup dominates the decoding of a
word (about 3 ms in a tree of 45,000 words), so large tables are stored as rows: one lookup per
row, whose `slot 64 l` reads the kernel shares within a declaration (about 0.17 ms per word), or
one literal read by `slotLookup`.

Source authentication and bounds on a decoded candidate are separate obligations.

## References

* IEEE Computer Society, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, IEEE,
  Piscataway, NJ, 2019, <https://doi.org/10.1109/IEEESTD.2019.8766229>. The binary64
  interchange format.
-/

@[expose] public section

namespace CAS.Numerics

/-- The exact unsigned magnitude represented by a binary64 word. -/
def binary64DyadicMagnitude (word : ℕ) : ℚ :=
  let exponent : ℕ := word / 2 ^ 52 % 2048
  let fraction : ℕ := word % 2 ^ 52
  if exponent = 0 then (fraction : ℚ) / 2 ^ 1074
  else if exponent = 2047 then 0
  else if 1075 ≤ exponent then
    ((2 ^ 52 + fraction : ℕ) : ℚ) * 2 ^ (exponent - 1075)
  else ((2 ^ 52 + fraction : ℕ) : ℚ) / 2 ^ (1075 - exponent)

/-- Decode a finite binary64 bit word to its exact signed dyadic rational. -/
def binary64DyadicValue (word : ℕ) : ℚ :=
  if word / 2 ^ 63 % 2 = 0 then binary64DyadicMagnitude word
  else -binary64DyadicMagnitude word

/-- The biased exponent field, bits 52 to 62 of a binary64 word. -/
def binary64ExponentField (word : ℕ) : ℕ := Nat.land (Nat.shiftRight word 52) 2047

/-- The exponent field as a quotient and a remainder. -/
theorem binary64ExponentField_eq (word : ℕ) :
    binary64ExponentField word = word / 2 ^ 52 % 2048 := by
  change (word >>> 52) &&& (2 ^ 11 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- The exponent field of every word is less than `2048`. -/
theorem binary64ExponentField_lt (word : ℕ) : binary64ExponentField word < 2048 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- The mask `2 ^ w - 1` of a slot of `w` bits, formed by a shift. -/
def slotMask (w : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 w) 1

/-- Slot `k` of width `w` of `x`: the bits `w * k` through `w * k + w - 1`. -/
def slot (w k x : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul w k)) (slotMask w)

/-- Exact word storage whose length is checked by the constructor types.
Balanced concatenations allow a lookup to reduce without visiting unrelated words. -/
inductive Binary64WordTree : ℕ → Type
  | empty : Binary64WordTree 0
  | singleton (word : ℕ) : Binary64WordTree 1
  | append {m n : ℕ} (left : Binary64WordTree m) (right : Binary64WordTree n) :
      Binary64WordTree (m + n)

namespace Binary64WordTree

/-- Read a word by descending only the branch containing its finite index. -/
def get {n : ℕ} : Binary64WordTree n → Fin n → ℕ
  | .empty, i => Fin.elim0 i
  | .singleton word, _ => word
  | @append m _ left right, i =>
    if h : i.val < m then left.get ⟨i.val, h⟩
    else right.get ⟨i.val - m, by have := i.isLt; omega⟩

/-- Decode an indexed word without any string or floating-point evaluation. -/
def value {n : ℕ} (words : Binary64WordTree n) (i : Fin n) : ℚ :=
  binary64DyadicValue (words.get i)

/-- The first `n` slots of width `w` of a packed natural number, appended one at a time. -/
def ofPackedSlotsLinear (w : ℕ) : (n packed : ℕ) → Binary64WordTree n
  | 0, _ => .empty
  | n + 1, packed => .append (ofPackedSlotsLinear w n packed) (.singleton (slot w n packed))

/-- The first `n` slots of width `w` of a packed natural number as a balanced tree. The left
half keeps the low slots and the right half reads a shifted copy, so a lookup computes only the
slots of its own branch. Each of the `depth` levels halves the length; `ofPackedSlotsLinear`
builds inputs of fewer than two slots and the inputs left when the depth is exhausted. -/
def ofPackedSlots (w : ℕ) : (depth n packed : ℕ) → Binary64WordTree n
  | 0, n, packed => ofPackedSlotsLinear w n packed
  | depth + 1, n, packed =>
    if h : 2 ≤ n then
      have e : n / 2 + (n - n / 2) = n := by omega
      e ▸ .append
        (ofPackedSlots w depth (n / 2) (Nat.land packed (slotMask (Nat.mul w (n / 2)))))
        (ofPackedSlots w depth (n - n / 2) (Nat.shiftRight packed (Nat.mul w (n / 2))))
    else ofPackedSlotsLinear w n packed

/-- The first `n` 64-bit words of a packed natural number as a balanced tree. -/
def ofPacked (depth n packed : ℕ) : Binary64WordTree n := ofPackedSlots 64 depth n packed

end Binary64WordTree

end CAS.Numerics

end

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- Pack `count` slot values of width `w` starting at `start`, the first value lowest, by
balanced shifts. -/
partial def packSlotValues (w : Nat) (values : Array Nat) (start count : Nat) : Nat :=
  if count = 0 then 0
  else if count = 1 then values[start]!
  else
    let left := count / 2
    packSlotValues w values start left |||
      (packSlotValues w values (start + left) (count - left) <<< (w * left))

/-- A depth of balanced halving that reaches single rows. -/
def packedTreeDepth (rows : Nat) : Nat := Nat.log2 rows + 1

/-- The term `Binary64WordTree.ofPackedSlots (w * columns) depth rows literal` for slot values
in row-major order. The literal holds entry `k` of row `i` in slot `columns * i + k` of width
`w` and is a named irreducible auxiliary definition. -/
def packedSlotRowsTerm (w columns : Nat) (slots : Array Nat) : TermElabM Expr := do
  unless 0 < columns && slots.size % columns == 0 do
    throwError "packed rows need a positive row length dividing the {slots.size} entries"
  if let some i := slots.findIdx? (fun v ↦ (1 <<< w) ≤ v) then
    throwError "slot value {i} does not fit {w} bits"
  let packed := packSlotValues w slots 0 slots.size
  let name ← mkAuxDeclName `_packedRows
  let literal ← mkCompactNatLiteral name packed
  -- The literal stays data during elaboration; kernel and compiled checks read its body.
  setReducibilityStatus name .irreducible
  let rows := slots.size / columns
  return mkApp4 (mkConst ``Binary64WordTree.ofPackedSlots) (mkNatLit (w * columns))
    (mkNatLit (packedTreeDepth rows)) (mkNatLit rows) literal

/-- `binary64_words% text` imports hexadecimal binary64 words as a balanced word tree. -/
syntax (name := binary64Words) "binary64_words% " term:max : term

/-- `binary64_word_rows% q text` imports hexadecimal binary64 words as rows of `q` words. -/
syntax (name := binary64WordRows) "binary64_word_rows% " num term:max : term

private def parseBinary64Words (text : String) : TermElabM (Array Nat) := do
  let bytes := text.toUTF8
  unless bytes.size % 16 == 0 do
    throwError "binary64 input must contain exactly 16 hexadecimal digits per word"
  let mut words := #[]
  for i in [:bytes.size / 16] do
    let mut word := 0
    for j in [:16] do
      let byte := bytes[16 * i + j]!.toNat
      let digit ← if 48 ≤ byte && byte ≤ 57 then pure (byte - 48)
        else if 97 ≤ byte && byte ≤ 102 then pure (byte - 87)
        else throwError "binary64 input contains a non-hexadecimal byte at {16 * i + j}"
      word := 16 * word + digit
    words := words.push word
  return words

/-- Import hexadecimal text as a balanced word tree built from one packed literal.
The elaborator parses data; its output is a named auxiliary definition applying
`Binary64WordTree.ofPacked` to natural literals. The name keeps expressions that use
the table small, and its compiled value is shared by every lookup. -/
@[term_elab binary64Words] def elabBinary64Words : TermElab := fun stx _ ↦ do
  let `(binary64_words% $text) := stx | throwUnsupportedSyntax
  let words ← parseBinary64Words (← evalString text)
  let name ← mkAuxDeclName `_binary64Words
  let packedName ← mkAuxDeclName `_binary64Packed
  let packed ← mkCompactNatLiteral packedName (packSlotValues 64 words 0 words.size)
  setReducibilityStatus packedName .irreducible
  let tree := mkApp3 (mkConst ``Binary64WordTree.ofPacked) (mkNatLit 64)
    (mkNatLit words.size) packed
  let result ← mkAuxDefinitionFor (compile := true) name tree
  -- The table stays data during elaboration; kernel and compiled checks read its body.
  setReducibilityStatus name .irreducible
  return result

/-- Import hexadecimal text as rows of `q` words. The output is
`Binary64WordTree.ofPackedSlots (64 * q) depth rows literal` with the literal of
`binary64_words%` as a named auxiliary definition, so one lookup returns a whole row and the
words of the row are its 64-bit slots. -/
@[term_elab binary64WordRows] def elabBinary64WordRows : TermElab := fun stx _ ↦ do
  let `(binary64_word_rows% $q:num $text) := stx | throwUnsupportedSyntax
  packedSlotRowsTerm 64 q.getNat (← parseBinary64Words (← evalString text))

end CAS.Numerics
