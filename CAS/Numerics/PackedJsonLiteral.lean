/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public meta import CAS.Numerics.Binary64

/-!
# Packed integer literals from JSON

`packed_int_literal% w n text key` reads the `n` entries of the integer column `key` of the
JSON document `text` (JSON integers or decimal strings; the column must hold exactly `n`) and
returns one natural literal holding entry `i` in slot `i` of width `w` as `x + 2 ^ w / 2`.
Entry `i` is `signedSlot w i literal`, and a row of `q` entries starting at `q * m` is the slot
`m` of width `w * q`, by `slot_slot_mul`.

## Implementation notes

`columnValues` of [Json](Json.lean) reads the column, and the biased entries are packed by
balanced shifts (`packSlotValues`) into one literal, stored by `mkCompactNatLiteral` as a named
irreducible auxiliary definition, as for `packed_int_rows%`. We build no tree: entries and rows
are slots of the literal at natural indices, so the `Nat.rec` loops of the kernel checks
([PackedSlots](PackedSlots.lean)) read them by shifts and masks, without a lookup or a `Fin`
index, and `slotLookup` reaches one entry of a large literal by halving. Importing a literal
establishes nothing about its entries; certificates check them.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `packed_int_literal% w n text key` imports `n` entries of the integer column `key` of the
JSON document `text` as one literal of biased slots of width `w`. -/
syntax (name := packedIntLiteral) "packed_int_literal% " num num term:max str : term

/-- Elaborate `packed_int_literal%`: read the entries, check that each fits a signed slot of `w`
bits, and return the packed literal. -/
@[term_elab packedIntLiteral] def elabPackedIntLiteral : TermElab := fun stx _ ↦ do
  let `(packed_int_literal% $w:num $n:num $text $key:str) := stx | throwUnsupportedSyntax
  let width := w.getNat
  let values ← columnValues (← evalString text) key.getString n.getNat
  let bias : Int := Int.ofNat ((1 <<< width) >>> 1)
  let bound : Int := Int.ofNat (1 <<< width)
  let slots ← values.mapIdxM fun i value ↦ do
    let biased := value + bias
    unless 0 ≤ biased && biased < bound do
      throwError "entry {i} = {value} does not fit a signed slot of {width} bits"
    pure biased.toNat
  let packed := packSlotValues width slots 0 slots.size
  let name ← mkAuxDeclName `_packedLiteral
  let literal ← mkCompactNatLiteral name packed
  -- The literal stays data during elaboration; kernel and compiled checks read its body.
  setReducibilityStatus name .irreducible
  return literal

end CAS.Numerics
