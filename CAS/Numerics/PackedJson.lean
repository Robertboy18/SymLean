/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public meta import CAS.Numerics.Binary64

/-!
# Packed integer rows from JSON

`packed_int_rows% w q text key` reads the integer column `key` of the JSON document `text`,
whose entries are JSON integers or decimal strings, and splits it into rows of `q` entries. The
expected type `Binary64WordTree rows` fixes the number of rows, and the column must hold
`rows * q` entries. The term is `Binary64WordTree.ofPackedSlots (w * q) depth rows packed`,
where the natural literal `packed` stores entry `x` of row `i` in slot `q * i + k` of width `w`
as `x + 2 ^ w / 2`. Row `i` of a table `t` is the natural number `t.get i`, entry `(i, k)` is
`signedSlot w k (t.get i)`, and `get_ofPackedSlots` with `slot_lt` bounds every row by
`2 ^ (w * q)`, as packed row combinations require. An entry that does not fit a signed slot
of `w` bits is an elaboration error.

## Implementation notes

`columnValues` of [Json](Json.lean) reads the column; Lean's JSON parser takes about 8 µs per
entry. `packedIntRowsTerm` biases and checks the entries, and `packedSlotRowsTerm` of
[Binary64](Binary64.lean) packs them by balanced shifts into one literal, so the table never
passes through numeral syntax ([PackedSlots](PackedSlots.lean) says why). `mkCompactNatLiteral`
stores it as a named irreducible auxiliary definition: the literal takes about `w / 8` bytes per
entry in the module data, and from `2 ^ 4096` on the decimal fields that compiled code reads add
`19` characters per `60` bits. Elaboration never unfolds the literal,
and kernel and compiled checks read it unchanged. The tree has depth `packedTreeDepth rows`,
enough to reach single rows, so a kernel lookup reduces only the masks and shifts of its own
branch. Importing a table establishes nothing about its entries; certificates check them.
`binary_grid_shard` ([BinaryGridShards](BinaryGridShards.lean)) stores its grid snapshots this
way.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- The tree term of a table of signed rows of `columns` entries in biased slots of width `w`,
with its literal as a named irreducible auxiliary definition. -/
def packedIntRowsTerm (w columns : Nat) (values : Array Int) : TermElabM Expr := do
  let bias : Int := Int.ofNat ((1 <<< w) >>> 1)
  let bound : Int := Int.ofNat (1 <<< w)
  let slots ← values.mapIdxM fun i value ↦ do
    let biased := value + bias
    unless 0 ≤ biased && biased < bound do
      throwError "entry {i} = {value} does not fit a signed slot of {w} bits"
    pure biased.toNat
  packedSlotRowsTerm w columns slots

/-- `packed_int_rows% w q text key` imports the integer column `key` of the JSON document
`text` as signed rows of `q` entries in biased slots of width `w`. The expected type
`Binary64WordTree rows` gives the number of rows. -/
syntax (name := packedIntRows) "packed_int_rows% " num num term:max str : term

/-- Elaborate `packed_int_rows%`: read `rows * q` entries of the column, check that each fits
a signed slot of `w` bits, and return the balanced tree of packed rows. -/
@[term_elab packedIntRows] def elabPackedIntRows : TermElab := fun stx expected ↦ do
  let `(packed_int_rows% $w:num $q:num $text $key:str) := stx | throwUnsupportedSyntax
  let some expected := expected
    | throwError "packed_int_rows% needs the expected type Binary64WordTree rows"
  let expected ← whnfR (← instantiateMVars expected)
  unless expected.isAppOfArity ``Binary64WordTree 1 do
    throwError "packed_int_rows% needs the expected type Binary64WordTree rows, not {expected}"
  let some rows ← (evalNat expected.appArg!).run
    | throwError "packed_int_rows% needs a numeral number of rows in {expected}"
  let values ← columnValues (← evalString text) key.getString (rows * q.getNat)
  packedIntRowsTerm w.getNat q.getNat values

end CAS.Numerics
