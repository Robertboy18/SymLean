/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public meta import CAS.Numerics.Binary64

/-!
# Compact packed rows

Three elaborators produce the same packed row trees as `packed_int_rows%`
(`Binary64WordTree.ofPackedSlots (w * q) depth rows packed`, entry `x` of row `i` in slot
`q * i + k` of width `w` as `x + 2 ^ w / 2`) from more compact sources.

* `hex_rows% w q text` and `hex_lower_rows% w q text` read signed entries written as
  variable-length hexadecimal numbers: the length `L` (one digit from `1` to `f`, or `0` and
  three digits) followed by `L` digits of the zigzag code (`2x` for `x ≥ 0`, `-2x - 1` for
  `x < 0`), in lowercase digits; bytes between entries that are not such digits, whitespace for
  instance, are skipped. `hex_rows%` reads `q` entries per row, `hex_lower_rows%` the entries
  `i, …, q - 1` of row `i` (the others are `0`).
* `computed_rows% w q f` evaluates the closed term `f : ℕ → Array ℕ` with compiled code at
  every row index and stores the `q` slot values `f i` (each below `2 ^ w`) as row `i`.

## Implementation notes

All three end in `packedSlotRowsTerm` of [Binary64](Binary64.lean), which packs the slots by
balanced shifts into one literal stored by `mkCompactNatLiteral`, marks it irreducible and
returns the row tree, so the result is the term that `packed_int_rows%` gives for the same slot
values. Only the source differs. The zigzag code makes the length of an entry follow its
magnitude, so the text of a table of entries of `b` bits takes about `b / 4 + 1` bytes per
stored entry, and the parser reads it in one pass over the bytes, with no JSON in between.
`computed_rows%` stores no source at all: the row function runs as compiled code during
elaboration, outside `withLiteralEnv`, so a compact literal it reads is parsed from its digits
once per process. Neither the parser nor the row function is trusted: the kernel sees only the
literal, which, as for `packed_int_rows%`, establishes nothing about its entries; certificates
check them. `centerRowSlots` ([CenterBlockChecks](CenterBlockChecks.lean)) is written to be
stored this way.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- The value of a hexadecimal digit, or `none`. -/
private def hexDigitValue (byte : UInt8) : Option Nat :=
  if 48 ≤ byte && byte ≤ 57 then some (byte.toNat - 48)
  else if 97 ≤ byte && byte ≤ 102 then some (byte.toNat - 87)
  else none

/-- Read `count` variable-length zigzag entries from the hexadecimal text. -/
private def parseZigzagHex (text : String) (count : Nat) : TermElabM (Array Int) := do
  let bytes := text.toUTF8
  let mut pos := 0
  let mut out : Array Int := Array.mkEmpty count
  for _ in [:count] do
    while pos < bytes.size && (hexDigitValue bytes[pos]!).isNone do
      pos := pos + 1
    let some len0 := (if pos < bytes.size then hexDigitValue bytes[pos]! else none)
      | throwError "hexadecimal rows end after {out.size} of {count} entries"
    pos := pos + 1
    let mut len := len0
    if len0 == 0 then
      len := 0
      for _ in [:3] do
        let some d := (if pos < bytes.size then hexDigitValue bytes[pos]! else none)
          | throwError "hexadecimal entry {out.size} has a cut-off length"
        len := 16 * len + d
        pos := pos + 1
    let mut z := 0
    for _ in [:len] do
      let some d := (if pos < bytes.size then hexDigitValue bytes[pos]! else none)
        | throwError "hexadecimal entry {out.size} is cut off"
      z := 16 * z + d
      pos := pos + 1
    out := out.push (if z % 2 == 0 then Int.ofNat (z / 2) else -Int.ofNat ((z + 1) / 2))
  return out

/-- The biased slots of signed entries of width `w`. -/
private def biasedSlots (w : Nat) (values : Array Int) : TermElabM (Array Nat) := do
  let bias : Int := Int.ofNat ((1 <<< w) >>> 1)
  let bound : Int := Int.ofNat (1 <<< w)
  values.mapIdxM fun i value ↦ do
    let biased := value + bias
    unless 0 ≤ biased && biased < bound do
      throwError "entry {i} = {value} does not fit a signed slot of {w} bits"
    pure biased.toNat

/-- The number of rows of the expected type `Binary64WordTree rows`. -/
private def expectedRows (name : String) (expected : Option Expr) : TermElabM Nat := do
  let some expected := expected
    | throwError "{name} needs the expected type Binary64WordTree rows"
  let expected ← whnfR (← instantiateMVars expected)
  unless expected.isAppOfArity ``Binary64WordTree 1 do
    throwError "{name} needs the expected type Binary64WordTree rows, not {expected}"
  let some rows ← (Meta.evalNat expected.appArg!).run
    | throwError "{name} needs a numeral number of rows in {expected}"
  return rows

/-- `hex_rows% w q text`: dense signed rows of `q` entries from variable-length hexadecimal. -/
syntax (name := hexRows) "hex_rows% " num num term:max : term

/-- `hex_lower_rows% w q text`: row `i` holds the entries of columns `i, …, q - 1`. -/
syntax (name := hexLowerRows) "hex_lower_rows% " num num term:max : term

/-- Elaborate `hex_rows%`: read `rows * q` zigzag entries, check that each fits a signed slot
of `w` bits, and return the balanced tree of packed rows. -/
@[term_elab hexRows] def elabHexRows : TermElab := fun stx expected ↦ do
  let `(hex_rows% $w:num $q:num $text) := stx | throwUnsupportedSyntax
  let rows ← expectedRows "hex_rows%" expected
  let values ← parseZigzagHex (← evalString text) (rows * q.getNat)
  packedSlotRowsTerm w.getNat q.getNat (← biasedSlots w.getNat values)

/-- Elaborate `hex_lower_rows%`: read the stored entries of columns `i, …, q - 1` of each row
`i`, set the columns below `i` to `0`, check that each entry fits a signed slot of `w` bits,
and return the balanced tree of packed rows. -/
@[term_elab hexLowerRows] def elabHexLowerRows : TermElab := fun stx expected ↦ do
  let `(hex_lower_rows% $w:num $q:num $text) := stx | throwUnsupportedSyntax
  let rows ← expectedRows "hex_lower_rows%" expected
  let cols := q.getNat
  unless rows ≤ cols do throwError "hex_lower_rows% needs at most {cols} rows"
  let count := (List.range rows).foldl (fun s i ↦ s + (cols - i)) 0
  let stored ← parseZigzagHex (← evalString text) count
  let mut values : Array Int := Array.mkEmpty (rows * cols)
  let mut pos := 0
  for i in [:rows] do
    for k in [:cols] do
      if i ≤ k then
        values := values.push stored[pos]!
        pos := pos + 1
      else
        values := values.push 0
  packedSlotRowsTerm w.getNat cols (← biasedSlots w.getNat values)

/-- Evaluate a closed row function during elaboration. -/
unsafe def evalRowFunUnsafe (term : TSyntax `term) : TermElabM (Nat → Array Nat) := do
  evalTerm (Nat → Array Nat)
    (← mkArrow (mkConst ``Nat) (mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat))) term

/-- The value of a closed row function, computed during elaboration. -/
@[implemented_by evalRowFunUnsafe]
opaque evalRowFun (term : TSyntax `term) : TermElabM (Nat → Array Nat)

/-- `computed_rows% w q f`: row `i` holds the `q` slot values `f i` (each below `2 ^ w`). -/
syntax (name := computedRows) "computed_rows% " num num term:max : term

/-- Elaborate `computed_rows%`: evaluate `f i` for every row `i`, check that it has `q` slot
values below `2 ^ w`, and return the balanced tree of packed rows. -/
@[term_elab computedRows] def elabComputedRows : TermElab := fun stx expected ↦ do
  let `(computed_rows% $w:num $q:num $f) := stx | throwUnsupportedSyntax
  let rows ← expectedRows "computed_rows%" expected
  let cols := q.getNat
  let fn ← evalRowFun f
  let mut slots : Array Nat := Array.mkEmpty (rows * cols)
  for i in [:rows] do
    let row := fn i
    unless row.size == cols do throwError "row {i} has {row.size} entries, not {cols}"
    slots := slots ++ row
  packedSlotRowsTerm w.getNat cols slots

end CAS.Numerics
