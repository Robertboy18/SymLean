/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import CAS.Numerics.Binary64
public import CAS.Numerics.Binary64

/-!
# Windows of packed slots

`json_slot_windows% w text key offsets n` reads the natural column `key` of the JSON document
`text` and the column `offsets` of `n + 1` nondecreasing positions in it, starting at zero and
ending at its length, and returns a function `ℕ → ℕ`: window `t` is one natural literal holding
the entries `offsets[t]` to `offsets[t + 1] - 1` of the column in slots of width `w`, the first
entry lowest; indices past the end return the last window. `json_slot_array% w text key n` reads
the `n` natural entries of `key`, a flat column or an array of rows read in order, as one literal
with entry `i` in slot `i`. The importers reject negative entries, entries of `2 ^ w` or more and
malformed offsets.

## Implementation notes

As for `json_slot_blocks%` ([SlotBlocks](SlotBlocks.lean)), each window is packed by balanced
shifts and stored by `mkCompactNatLiteral` as a named irreducible auxiliary definition, and a
balanced `cond` tree on the window index selects it. Unlike blocks, windows may have different
lengths, so groups of entries of different sizes need no padding to a common block length. A
check that reads many entries of one window selects the window once and then shifts and masks
its literal. `json_slot_array%` keeps the whole table in one literal, read by shifts and masks
at natural indices. Importing a table establishes nothing about its entries; certificates check
them.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `json_slot_windows% w text key offsets n` imports the `n` windows of the natural column `key`
delimited by the column `offsets`, one literal of `w`-bit slots per window. -/
syntax (name := jsonSlotWindows) "json_slot_windows% " num term:max str str num : term

/-- `json_slot_array% w text key n` imports the `n` natural entries of `key`, a flat array or an
array of rows, as one literal of `w`-bit slots. -/
syntax (name := jsonSlotArray) "json_slot_array% " num term:max str num : term

/-- The natural entries of a JSON array, each below `2 ^ width`. -/
private def windowEntries (key : String) (width : Nat) (entries : Array Json) :
    TermElabM (Array Nat) :=
  entries.mapIdxM fun i entry ↦ do
    match integerEntry entry with
    | .ok value =>
      unless 0 ≤ value && value < Int.ofNat (1 <<< width) do
        throwError "JSON column '{key}', entry {i}: {value} does not fit {width} bits"
      pure value.toNat
    | .error error => throwError "JSON column '{key}', entry {i}: {error}"

/-- A balanced `cond` tree on the bound index selecting the literals `lo` to `hi - 1`. -/
private partial def windowTree (literals : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then literals[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (mkConst ``cond [Level.one]) (mkConst ``Nat)
      (mkApp2 (mkConst ``Nat.blt) (.bvar 0) (mkNatLit mid))
      (windowTree literals lo mid) (windowTree literals mid hi)

/-- One named irreducible literal per window `[bounds[t], bounds[t + 1])` of `slots`, and the
selector over them. -/
private def windowSelector (width : Nat) (slots : Array Nat) (bounds : Array Nat) :
    TermElabM Expr := do
  let mut literals := #[]
  for t in [:bounds.size - 1] do
    let start := bounds[t]!
    let name ← mkAuxDeclName `_slotWindow
    let literal ← mkCompactNatLiteral name
      (packSlotValues width slots start (bounds[t + 1]! - start))
    -- Windows stay data during elaboration; kernel and compiled checks read their bodies.
    setReducibilityStatus name .irreducible
    literals := literals.push literal
  return mkLambda `window .default (mkConst ``Nat) (windowTree literals 0 literals.size)

/-- Elaborate `json_slot_windows%`: read the column and its offsets, check the offsets, and pack
each window into a named literal. -/
@[term_elab jsonSlotWindows] def elabJsonSlotWindows : TermElab := fun stx _ ↦ do
  let `(json_slot_windows% $w:num $text $key:str $offsets:str $n:num) := stx
    | throwUnsupportedSyntax
  let json ← ofExcept (Json.parse (← evalString text))
  let width := w.getNat
  let slots ← windowEntries key.getString width
    (← ofExcept (json.getObjValAs? (Array Json) key.getString))
  let bounds ← windowEntries offsets.getString 64
    (← ofExcept (json.getObjValAs? (Array Json) offsets.getString))
  unless 0 < width && 0 < n.getNat && bounds.size == n.getNat + 1 do
    throwError "json_slot_windows% needs a positive width and {n.getNat + 1} offsets"
  unless bounds[0]! == 0 && bounds[n.getNat]! == slots.size do
    throwError "the offsets must start at zero and end at the column length {slots.size}"
  for t in [:n.getNat] do
    unless bounds[t]! ≤ bounds[t + 1]! do
      throwError "offset {t + 1} decreases"
  windowSelector width slots bounds

/-- Elaborate `json_slot_array%`: read the entries, flattening rows, and pack them into one named
literal. -/
@[term_elab jsonSlotArray] def elabJsonSlotArray : TermElab := fun stx _ ↦ do
  let `(json_slot_array% $w:num $text $key:str $n:num) := stx | throwUnsupportedSyntax
  let json ← ofExcept (Json.parse (← evalString text))
  let width := w.getNat
  let entries ← ofExcept (json.getObjValAs? (Array Json) key.getString)
  let mut slots := #[]
  for entry in entries do
    match entry.getArr? with
    | .ok row => slots := slots ++ (← windowEntries key.getString width row)
    | .error _ => slots := slots ++ (← windowEntries key.getString width #[entry])
  unless 0 < width && slots.size == n.getNat do
    throwError "'{key.getString}' has {slots.size} entries; expected {n.getNat}"
  let name ← mkAuxDeclName `_slotArray
  let literal ← mkCompactNatLiteral name (packSlotValues width slots 0 slots.size)
  -- The literal stays data during elaboration; kernel and compiled checks read its body.
  setReducibilityStatus name .irreducible
  return literal

end CAS.Numerics
